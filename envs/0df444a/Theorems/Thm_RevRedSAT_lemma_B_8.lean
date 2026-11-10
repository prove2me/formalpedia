-- Prove2me | Theorems.Thm_RevRedSAT_lemma_B_8
-- name    : RevRedSAT.lemma_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:34.328875+00:00
-- url     : https://prove2.me/theorems/37c97163-8509-4cb8-8b78-e9a702540d46
-- title:
--   Lemma B.8 — returned families have frequency at most $T_d(\delta)\le(2d/\delta)^{4d}$
-- statement:
--   Let $d\ge2$, $\delta=2^{-j}$ with $j\ge2$, $A=2d/\delta$ and $t_p=A^{4p}/(4d)$.
--
--   1. Every reduced, sparse family of nonempty sets of size at most $d$ (in particular every family returned by the sparsification recursion) has frequency at most $T_d(\delta)=1+\sum_{p=1}^{d-1}t_p$.
--   2. $T_d(\delta)=O_d(\delta^{-(4d-4)})$: there is $C_d$ with $T_d(\delta)\le C_d\,\delta^{-(4d-4)}$ for all $j\ge2$.
--   3. $T_d(\delta)\le(2d/\delta)^{4d}$.
--
--   The statement covers $d=2$.
--
--   Differences from the source:
--   - generalization: every family returned by the recursion → every reduced, sparse family of nonempty sets of rank at most d; reason: returned families have these properties (p.87–88) and the proof uses only them; the source's claim is the special case
--   - encoding: O_d(δ^{−(4d−4)}) → ∃ C_d, ∀ j ≥ 2, T_d(δ) ≤ C_d δ^{−(4d−4)}; reason: the meaning of O_d
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.8, p.91 (printed) = PDF p.93

import Mathlib
import Definitions.Def_RevRedSAT_mu
import Definitions.Def_RevRedSAT_frequency

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma B.8 (the terminal frequency bound).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma B.8, p.91: "Let A = 2d/δ and t_p = A^{4p}/(4d) for 1 ≤ p ≤ d − 1. Every family returned by
the recursion above has frequency at most 1 + Σ_{p=1}^{d−1} t_p = T_d(δ) = O_d(δ^{−(4d−4)}). In
particular, this is at most the conservative bound (2d/δ)^{4d}. The statement holds also for d = 2."

For every `d ≥ 2`:
1. every reduced, sparse family of rank at most `d` with nonempty members has frequency at most
   `T_d(δ)`, for every `δ = 2^{−j}`, `j ≥ 2`;
2. there is `C_d` with `T_d(δ) ≤ C_d·δ^{−(4d−4)}` for every `j ≥ 2`;
3. `T_d(δ) ≤ (2d/δ)^{4d}` for every `j ≥ 2`.

**Formalization Note** The returned families are reduced, sparse, of rank at most `d`, with
nonempty members (App. B, p.87–88); clause 1 is stated for every such family. -/
theorem lemma_B_8 (d : ℕ) (hd : 2 ≤ d) :
    (∀ (j n : ℕ) (F : Finset (Finset (Fin n))), 2 ≤ j → (∀ S ∈ F, S.card ≤ d) →
      (∀ S ∈ F, S.Nonempty) → IsReduced F → IsSparse d j F → (frequency F : ℝ) ≤ Td d j) ∧
    (∃ C : ℝ, ∀ j : ℕ, 2 ≤ j → Td d j ≤ C * deltaOf j ^ (-((4 * d - 4 : ℕ) : ℤ))) ∧
    (∀ j : ℕ, 2 ≤ j → Td d j ≤ (2 * d / deltaOf j) ^ (4 * d)) := by sorry

end RevRedSAT
