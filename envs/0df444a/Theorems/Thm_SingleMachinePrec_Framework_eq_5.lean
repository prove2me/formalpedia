-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_eq_5
-- name    : SingleMachinePrec.Framework.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:48:58.233649+00:00
-- url     : https://prove2.me/theorems/c93e0f37-6716-4bb8-b420-689a9027d381
-- title:
--   Eq. (5) — the expected weight of I_{1/2} is at least (k/t) · w(V_{1/2})
-- statement:
--   Let $S$ be an instance of $1|\mathrm{prec}|\sum w_jC_j$ with precedence order $P$ and node weights $w_{(i,j)} = p_i w_j \ge 0$, let $L_1,\dots,L_t$ be a $k:t$-realizer of $P$, and let $x$ be a vector indexed by the incomparable pairs, with $V_{1/2} = \{u : x_u = \tfrac12\}$. For each $i$ let $I_{1/2}(L_i)$ be the set of pairs of $V_{1/2}$ reversed in $L_i$. Then
--   $$\frac1t \sum_{i=1}^t w\bigl(I_{1/2}(L_i)\bigr) \;\ge\; \frac kt\, w(V_{1/2}).$$
--
--   The left side is the expected weight $\mathrm E[w(I_{1/2})]$ when $L$ is drawn uniformly from the realizer. The bound feeds the estimate (6) of the expected weight of the rounded cover.
--
--   **Formalization Note** The expectation is the uniform average over the $t$ indices. The statement holds for any $x$, not only half-integral optimal ones; only $V_{1/2}$ enters.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 659, Eq. (5) (proof of Theorem 5.1)

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

namespace SingleMachinePrec.Framework

/-- **Eq. (5)** (p. 659). Let `L_1, …, L_t` be a `k : t`-realizer of the precedence order of `S`
and `x` any vector indexed by the incomparable pairs. The average over `i` of the weight of
`I_{1/2}(L_i)`, the pairs of `V_{1/2}` reversed in `L_i`, is at least `(k/t) · w(V_{1/2})`. -/
theorem eq_5 {N : Type*} [Fintype N] (S : Instance N) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) :
    ((k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
      (1 / (t : ℝ)) * ∑ i, weight S (reversedHalf x (L i)) := by sorry

end SingleMachinePrec.Framework
