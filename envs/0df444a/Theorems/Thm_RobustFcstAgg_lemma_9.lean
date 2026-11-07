-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_9
-- name    : RobustFcstAgg.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:45:22.826418+00:00
-- url     : https://prove2.me/theorems/2cdeb72e-79ab-4599-9ff5-f053a5bb47c0
-- title:
--   Lemma 9 (corrected: uniqueness for $n\ge2$ or $d\le1$) — equioscillation characterizes the minimizer on $[1,n]$
-- statement:
--   Let $n\ge1$. A polynomial $p^*\in P_d$ with $p^*(0)=1$ minimizes $\max_{x\in[1,n]}|p(x)|$ over $p\in P_d$, $p(0)=1$, if and only if it equioscillates at $d+1$ points of $[1,n]$: there exist $1\le x_0\le\dots\le x_d\le n$ and $\sigma\in\{-1,+1\}$ with
--   $$p^*(x_i)=\sigma(-1)^i\max_{x\in[1,n]}|p^*(x)|.$$
--   Moreover, if $n\ge2$ or $d\le1$, the minimizer exists and is unique.
--
--   This is the analogue of the classical equioscillation theorem under the constraint $p(0)=1$.
--
--   Differences from the source:
--   - correction: the minimizer is unique, for every n → unique when 2 ≤ n or d ≤ 1 (the equivalence is stated for every n ≥ 1); reason: at n = 1, d = 2, the polynomials 1 − x and 1 − x² are distinct minimizers, both with value 0 on [1, 1]
--   - reading: p* equioscillates at d + 1 points → the equivalence is stated for p with natDegree ≤ d and p(0) = 1; reason: the left side requires it; otherwise a rescaled Chebyshev polynomial is a counterexample
--   - reading: the polynomial p* is unique → there is exactly one minimizer; reason: existence is implicit in "arg min" and in the use made of the lemma on p.29
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 9, p.27; proof pp.28–29

import Mathlib
import Definitions.Def_RobustFcstAgg_IsIvlMinimizer
open Polynomial

namespace RobustFcstAgg

/-- **Lemma 9 (corrected: uniqueness for `n ≥ 2` or `d ≤ 1`).** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 9, p.27 (proof pp.28–29): `p*` minimizes `max_{t ∈ [1,n]} |p(t)|` over `p ∈ P_d`,
`p(0) = 1`, if and only if it equioscillates at `d + 1` points of `[1, n]`; moreover, the polynomial is unique.

**Formalization Note.** The equivalence is stated for every `n ≥ 1`. The uniqueness clause assumes `n ≥ 2` or `d ≤ 1`; this is a
correction: at `n = 1`, `d = 2`, both `1 − x` and `1 − x²` attain the value `0` on `[1, 1]`. The equivalence is stated for
`p ∈ P_d` with `p(0) = 1`, as the left side requires. `E` is `max_{x ∈ [1,n]} |p(x)|`. -/
theorem lemma_9 (n d : ℕ) (hn : 1 ≤ n) :
    (∀ p : ℝ[X], p.natDegree ≤ d → p.eval 0 = 1 →
      (IsIvlMinimizer n d p ↔
        ∃ E, IsGreatest ((fun x => |p.eval x|) '' Set.Icc (1 : ℝ) n) E ∧
          ∃ x : Fin (d + 1) → ℝ, Monotone x ∧ (∀ i, x i ∈ Set.Icc (1 : ℝ) n) ∧
            ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i, p.eval (x i) = σ * (-1) ^ (i : ℕ) * E)) ∧
    (2 ≤ n ∨ d ≤ 1 → ∃! p : ℝ[X], IsIvlMinimizer n d p) := by sorry

end RobustFcstAgg
