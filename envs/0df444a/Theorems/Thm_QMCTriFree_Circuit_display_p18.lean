-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_display_p18
-- name    : QMCTriFree.Circuit.display_p18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:58.33709+00:00
-- url     : https://prove2.me/theorems/5a1dca63-438f-4415-9db4-9fdd17f1499a
-- title:
--   Display after Lemma 18 — at $\beta=0.39$ ($\beta^*\approx0.390$), $F(\beta;x)\ge0.582\,(1+x)$ on $[-1,1]$
-- statement:
--   With $F(\beta;x)$ the function of Algorithm 17, step 4, and $\beta=39/100$,
--   $$F\bigl(0.39;\,x\bigr)\ \ge\ 0.582\,(1+x)\qquad\text{for all }x\in[-1,1].$$
--
--   The paper chooses $\beta^*=\arg\max_\beta\min_x F(\beta,x)/(1+x)\approx0.390$ and reports $\min_xF(\beta^*,x)/(1+x)\approx0.5828$; this statement is the exact inequality the proof of Theorem 19 needs, at an explicit value of $\beta$ close to $\beta^*$.
--
--   **Formalization Note** The constants are exact rationals. Numerically the margin $\min_x\bigl(F(0.39;x)-0.582(1+x)\bigr)\approx0.0011$ is small (attained near $x\approx0.33$), so a proof needs certified bounds on ${}_2F_1$.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 18, display after Lemma 18 (and Figure 5)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 18, display after Lemma 18 (`min_x F(β*, x)/(1 + x) ≈ 0.5828`,
`β* ≈ 0.390`), at `β = 0.39`: `F(0.39; x) ≥ 0.582 (1 + x)` for all `x ∈ [−1, 1]`. -/
theorem display_p18 :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, (582 / 1000 : ℝ) * (1 + x) ≤ Fβ (39 / 100) x := by sorry

end QMCTriFree.Circuit
