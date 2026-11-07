-- Prove2me | Theorems.Thm_SmolenskyAC_theorem_1
-- name    : SmolenskyAC.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:45.358836+00:00
-- url     : https://prove2.me/theorems/47dfbdec-abd2-47c5-b250-3f7d872fedd6
-- title:
--   Theorem 1 — a small depth-$k$ circuit differs from any complete set on $2^{n-1}-o(2^n)$ assignments
-- statement:
--   Let $F$ be a field and fix a basis in which every flagged kind is nearly $F$-easy and every other kind is $F$-easy, with one constant $\lambda$. Let $k\ge1$ and let $C^n$ be circuits on $n$ inputs of depth at most $k$, with outputs $g^n_1,\dots,g^n_s$ indexed by a finite set, and with at most $\exp(r(n))$ flagged gates where $r(n)=o(n^{1/(2k)})$. Let $f^n_1,\dots,f^n_s\in U^n_F$ be a $U^n_F$-complete family indexed by the same set. Then there is $e(n)=o(2^n)$ such that for every $n$
--
--   $$\#\{x\in D^n:\ g^n_i(x)\ne f^n_i(x)\ \text{for some } i\}\ \ge\ 2^{n-1}-e(n),$$
--
--   the outputs being read in $F$.
--
--   This is the paper's general lower bound: a small circuit of nearly easy and easy gates cannot agree with a complete set on much more than half the cube.
--
--   Differences from the source:
--   - generalization: a circuit is a transitively closed set whose only minimal elements are the inputs and whose maximal elements are the outputs (p.78) → gates listed in topological order, sources among inputs, Boolean constants and earlier gates; repeated wires, empty fan-in and gates feeding no output allowed; reason: the page's circuits are the special case without constants, repeats or dangling gates, and every gate of such a circuit is counted in both models
--   - generalization: a depth k circuit → depth at most k; reason: a circuit of depth exactly k is one case
--   - generalization: NOT takes one input → a NOT gate may have any fan-in and negates its first source (true with none); reason: a page NOT gate is the fan-in 1 case; the extra sources are ignored, and they only increase the depth
--   - encoding: a collection of circuits C^n, one per input length, with o(·) in n (Remark, p.78) → a family indexed by every n; the o(·) witnesses are chosen after the family; reason: the Remark's meaning of the superscript n
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: each basic operation has its own constant λ → one constant λ for all gate kinds; reason: for a finite basis take the largest λ; both notions are monotone in λ
--   - encoding: the exponent 1/2k → 1/(2k) with k ≥ 1; reason: the printed stacked fraction; at k = 0 the exponent is undefined
--   - generalization: exp(o(n^(1/2k))) nearly F-easy gates → at most exp(r(n)) flagged gates, r = o(n^(1/(2k))); reason: a count of exactly that size is one case
--   - encoding: 2^(n−1) → 2^n / 2 in ℝ; reason: no truncated subtraction at n = 0
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Theorem 1, p.81 (pdf 5)

import Mathlib
import Definitions.Def_SmolenskyAC_Circuit
import Definitions.Def_SmolenskyAC_Easy
import Definitions.Def_SmolenskyAC_UComplete

open Asymptotics Filter

namespace SmolenskyAC

open Classical in
/-- **Theorem 1** (Smolensky, STOC 1987, p.81): suppose a depth `k` circuit `C^n` uses
`exp(o(n^{1/2k}))` nearly `F`-easy gates and an arbitrary number of `F`-easy gates. Then the output
`g` (or the outputs `g_1, …, g_s`) of `C^n` differ from any `U^n_F`-complete element `f` (or set
`f_1, …, f_s`) on `2^{n−1} − o(2^n)` assignments.

**Formalization Note.** Families indexed by `n` (Remark, p.78). Outputs and the complete set are
indexed by the same finite type `ι n`; an assignment `x` counts when some output differs from the
corresponding `f_i` at `x`, read in `F` (the page's "for some `i`, `g_i` differs from `f_i`"). The
`f_i` are arbitrary elements of `U^n_F`, not necessarily Boolean. `2^{n−1}` is `2^n / 2` in `ℝ`,
and `e` is chosen after the families. -/
theorem theorem_1 (F : Type*) [Field F] {K : Type*} (op : K → Operation) (flag : K → Bool)
    (lam : ℕ) (heasy : ∀ κ, flag κ = false → IsFEasy F lam (op κ))
    (hnear : ∀ κ, flag κ = true → IsNearlyFEasy F lam (op κ))
    (k : ℕ) (hk : 1 ≤ k) {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (C : ∀ n, Circuit K n (ι n)) (hdepth : ∀ n, (C n).depth ≤ k)
    (r : ℕ → ℝ) (hr : r =o[atTop] fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))))
    (hcount : ∀ n, ((C n).countFlag flag : ℝ) ≤ Real.exp (r n))
    (f : ∀ n, ι n → Cube n → F) (hf : ∀ n, IsUComplete (f n)) :
    ∃ e : ℕ → ℝ, e =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) ∧
      ∀ n, (2 : ℝ) ^ n / 2 - e n ≤
        ((Finset.univ.filter fun x : Cube n =>
          ∃ i : ι n, (toF ((C n).eval op x i) : F) ≠ f n i x).card : ℝ) := by sorry

end SmolenskyAC
