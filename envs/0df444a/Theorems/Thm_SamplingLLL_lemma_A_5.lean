-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_5
-- name    : SamplingLLL.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:49.673944+00:00
-- url     : https://prove2.me/theorems/a8770fd7-4d06-4a51-9220-e8630f11b1cc
-- title:
--   Lemma A.5, (7), (8), pp.21–22 — signed reciprocal factory
-- statement:
--   Let update tasks be indexed by a well-founded set, and suppose
--   $$
--   r_i=\sum_{t\in T_i}\epsilon_ta_t\prod_{j\in C_t}(1-r_j)^{-1},\tag{5}\qquad a_t\le B_iq_i(t)\prod_{j\in C_t}s_j,\tag{6}
--   $$
--   with $0<B_i<1$, $s_i=1-B_i$, an executable proposal $q_i$ and an exact local operation of acceptance probability $a_t/[B_iq_i(t)\prod_{j\in C_t}s_j]$. Then the procedures of the factory produce
--   1. a variable $Y_i\in\{-B_i,0,B_i\}$ with $\mathbb EY_i=r_i$;
--   2. a coin of bias $s_i/(1-r_i)$; and
--   3. a retained label with $\mathbb P(\mathrm{Term}_i=t)=\frac{a_t}{B_i}\prod_{j\in C_t}(1-r_j)^{-1}$.
--
--   Moreover $r_i\le B_i$; the aggregate number of direct type-$j$ coin requests of one reciprocal coin is at most
--   $$
--   M_{ij}=\frac2{s_i}\sum_{t\in T_i}m_j(C_t)a_t\prod_{r\in C_t}s_r^{-1};\tag{7}
--   $$
--   the generator has mass $w_t=a_t\prod_{j\in C_t}(1-r_j)^{-1}$ on $t$; and $\sum_tw_t\le B_i<1$ (8).
--
--   **Formalization Note** The response is read off a coin whose child coins have the exact laws and count only type $j$.
--
--   Differences from the source:
--   - reading: "$r_i\ge0$ follows from its meaning as a conditional probability", with the $r_i$ of an abstract recursion → the hypothesis $0\le r_i$ on any solution of (5); reason: the abstract recursion gives no such meaning; the paper's $r_i$ satisfy it
--   - encoding: a well-founded set of tasks → a type with a rank in $\mathbb N$, and coins by level (`coinLevel`), for every level above the rank; reason: finite recursions have such a rank; strictness is the hypothesis `hstrict`, restricted to transcripts with $a_t>0$, the only ones with calls
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.5, eqs. (5)–(8), pp.21–22

import Mathlib
import Definitions.Def_SamplingLLL_Factory

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- Lemma A.5 (Signed reciprocal factory), with (7) and (8), pp.21–22. Update tasks are indexed by a type with
a rank (a well-founded set in which all calls have strict type); `T i` are the transcripts of `i`; `r` is any
nonnegative solution of (5), and (6) is the envelope. The procedures are those of `Factory`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.5, eqs. (5)–(8), pp.21–22.

**Formalization Note.** The value of `experiment` is `Y_i = ε_t B_i`, so `E Y_i = r_i` is
`B_i · signedMass = r_i`. The exact local operation enters through its acceptance probability
`a_t/[B_i q_i(t) ∏_{j∈C_t} s_j]`. The response (7) is read off a coin running on `stubCoin`, whose child coins
have the exact laws and count only type `j`, with weight `0` for the coin itself; its expected calls are then the
aggregate number of direct type-`j` requests. The paper reads `r_i ≥ 0` from `r_i` being a conditional
probability, so nonnegativity is a hypothesis on `r`. -/
theorem lemma_A_5 {ι τ Mk : Type} [DecidableEq ι] (F : Factory ι τ Mk) (rank : ι → ℕ)
    (T : ι → Finset τ) (a : ι → τ → ℝ) (r : ι → ℝ)
    (ha : ∀ i t, 0 ≤ a i t) (hr0 : ∀ i, 0 ≤ r i)
    (hsgn : ∀ t, F.sgn t = 1 ∨ F.sgn t = -1)
    (hB0 : ∀ i, 0 < F.budget i) (hB1 : ∀ i, F.budget i < 1)
    (hprop : ∀ i, mass (F.propose i) = 1)
    (hsupp : ∀ i t q u, F.propose i (some (t, q), u) ≠ 0 → t ∈ T i ∧ (q : ℝ) = F.qOf i t)
    (hlocalM : ∀ i t q u, F.propose i (some (t, q), u) ≠ 0 → mass (F.localOp i t q) = 1)
    (hlocal : ∀ i t q u, F.propose i (some (t, q), u) ≠ 0 →
      probOf (F.localOp i t q) (fun o => o ≠ none) =
        ENNReal.ofReal (a i t / ((F.budget i : ℝ) * (q : ℝ) *
          ((F.kids i t).map F.sOf).prod)))
    (hstrict : ∀ i, ∀ t ∈ T i, 0 < a i t → ∀ j ∈ F.kids i t, rank j < rank i)
    (h5 : ∀ i, r i = ∑ t ∈ T i,
      (F.sgn t : ℝ) * a i t * ((F.kids i t).map fun j => (1 - r j)⁻¹).prod)
    (h6 : ∀ i, ∀ t ∈ T i,
      a i t ≤ (F.budget i : ℝ) * F.qOf i t * ((F.kids i t).map F.sOf).prod)
    (i : ι) :
    r i ≤ (F.budget i : ℝ) ∧
    (∑ t ∈ T i, a i t * ((F.kids i t).map fun j => (1 - r j)⁻¹).prod) ≤ (F.budget i : ℝ) ∧
    (∀ j : ι, expCalls (F.coinAt (fun _ => 0) (F.stubCoin r j) i) ≤
      ENNReal.ofReal (2 / F.sOf i * ∑ t ∈ T i, ((F.kids i t).count j : ℝ) * a i t *
        ((F.kids i t).map fun l => (F.sOf l)⁻¹).prod)) ∧
    ∀ (w : ι → ℕ) (k : ℕ), rank i ≤ k →
      (F.budget i : ℝ) * F.signedMass (F.experiment (F.coinLevel w k) i) = r i ∧
      mass (F.coinLevel w (k + 1) i) = 1 ∧
      law (F.coinLevel w (k + 1) i) true = ENNReal.ofReal (F.sOf i / (1 - r i)) ∧
      (∀ t ∈ T i, probOf (F.experiment (F.coinLevel w k) i) (fun o => ∃ mk, o = some (t, mk)) =
        ENNReal.ofReal (a i t / (F.budget i : ℝ) *
          ((F.kids i t).map fun j => (1 - r j)⁻¹).prod)) ∧
      (∀ t ∈ T i, probOf (F.generator (F.coinLevel w k) i) (fun o => ∃ mk, o = some (t, mk)) =
        ENNReal.ofReal (a i t * ((F.kids i t).map fun j => (1 - r j)⁻¹).prod)) := by sorry

end SamplingLLL
