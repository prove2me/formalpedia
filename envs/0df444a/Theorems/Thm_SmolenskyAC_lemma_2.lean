-- Prove2me | Theorems.Thm_SmolenskyAC_lemma_2
-- name    : SmolenskyAC.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:32.496405+00:00
-- url     : https://prove2.me/theorems/f8eaf502-ddda-4f35-936e-8526375a77e4
-- title:
--   Lemma 2 — a small depth-$k$ circuit has degree $o(\sqrt n)$ in an algebra of dimension $2^n-o(2^n)$
-- statement:
--   Let $F$ be a field and fix a circuit basis in which every flagged gate kind is nearly $F$-easy and every other kind is $F$-easy, all with one constant $\lambda$. Let $k\ge 1$ and let $C^n$, $n\ge 0$, be circuits on $n$ inputs of depth at most $k$ with finitely many outputs, such that $C^n$ has at most $2^{r(n)}$ flagged gates, where
--
--   $$r(n)=o\big(n^{1/(2k)}\big).$$
--
--   Then there are sets $E_n\subseteq D^n$ and a function $d(n)$ with $|E_n|=o(2^n)$ and $d(n)=o(\sqrt n)$ such that every output of $C^n$, read in $F$, has degree at most $d(n)$ in $A^n=U^n_F/I_{E_n}$, i.e. coincides outside $E_n$ with a polynomial of total degree at most $d(n)$.
--
--   This is the approximation half of the method: a small circuit is a low-degree polynomial on all but a vanishing fraction of the cube. F-easy gates (NOT, $\mathrm{MOD}_p$) may be used in any number.
--
--   Differences from the source:
--   - generalization: a circuit is a transitively closed set whose only minimal elements are the inputs and whose maximal elements are the outputs (p.78) → gates listed in topological order, sources among inputs, Boolean constants and earlier gates; repeated wires, empty fan-in and gates feeding no output allowed; reason: the page's circuits are the special case without constants, repeats or dangling gates, and every gate of such a circuit is counted in both models
--   - generalization: a depth k circuit → depth at most k; reason: a circuit of depth exactly k is one case
--   - generalization: NOT takes one input → a NOT gate may have any fan-in and negates its first source (true with none); reason: a page NOT gate is the fan-in 1 case; the extra sources are ignored, and they only increase the depth
--   - encoding: a collection of circuits C^n, one per input length, with o(·) in n (Remark, p.78) → a family indexed by every n; the o(·) witnesses are chosen after the family; reason: the Remark's meaning of the superscript n
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: each basic operation has its own constant λ → one constant λ for all gate kinds; reason: for a finite basis take the largest λ; both notions are monotone in λ
--   - encoding: the exponent 1/2k → 1/(2k) with k ≥ 1; reason: the printed stacked fraction; at k = 0 the exponent is undefined
--   - generalization: 2^r nearly F-easy gates → at most 2^(r n) flagged gates, r real-valued; reason: a count of exactly 2^r is one case
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Lemma 2, p.80 (pdf 4)

import Mathlib
import Definitions.Def_SmolenskyAC_Circuit
import Definitions.Def_SmolenskyAC_Easy

open Asymptotics Filter

namespace SmolenskyAC

/-- **Lemma 2** (Smolensky, STOC 1987, p.80): let `C^n` be a depth `k` circuit that has an
arbitrary number of `F`-easy gates and `2^r` nearly `F`-easy gates, where `r` is `o(n^{1/2k})`.
Then there is an algebra `A^n ∈ Ω^n_F` of dimension `2^n − o(2^n)` such that all outputs of `C^n`
have degree `o(√n)` in `A^n`.

**Formalization Note.** A family of circuits `C n` on `n` inputs (the Remark of p.78), with gate
kinds `K` interpreted by `op`; the kinds flagged by `flag` are nearly `F`-easy and the others
`F`-easy, all with one constant `λ`. The algebras are erased sets `E n`; "dimension
`2^n − o(2^n)`" is `|E n| = o(2^n)`. The degree bound `d` is chosen after the family. -/
theorem lemma_2 (F : Type*) [Field F] {K : Type*} (op : K → Operation) (flag : K → Bool)
    (lam : ℕ) (heasy : ∀ κ, flag κ = false → IsFEasy F lam (op κ))
    (hnear : ∀ κ, flag κ = true → IsNearlyFEasy F lam (op κ))
    (k : ℕ) (hk : 1 ≤ k) {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (C : ∀ n, Circuit K n (ι n)) (hdepth : ∀ n, (C n).depth ≤ k)
    (r : ℕ → ℝ) (hr : r =o[atTop] fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))))
    (hcount : ∀ n, ((C n).countFlag flag : ℝ) ≤ (2 : ℝ) ^ (r n)) :
    ∃ (E : ∀ n, Finset (Cube n)) (d : ℕ → ℝ),
      (fun n => ((E n).card : ℝ)) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) ∧
      d =o[atTop] (fun n : ℕ => Real.sqrt n) ∧
      ∀ n (i : ι n), (degOff (E n) (fun x => (toF ((C n).eval op x i) : F)) : ℝ) ≤ d n := by sorry

end SmolenskyAC
