-- Prove2me | Theorems.Thm_PsiUniformBound
-- name    : PsiUniformBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:08.411032+00:00
-- url     : https://prove2.me/theorems/452886cf-8ba9-4c9d-a940-d47b1786922f
-- title:
--   Psi Uniform Bound: Psi Uniform Bound
-- statement:
--   The a priori two-sided bound on `ψ_{m,Q,ε,C}` used for integrability: for `m ≥ 1`,
--   `ε ≥ 0` and `C ≥ 0`, the quantity `ψ_{m,Q,ε,C}(γ)` of `\noderef{psi}` is nonnegative and
--   bounded above by `2C²·length(γ) + 2C²·length(γ)²/m`, a quantity depending only on `m`, `C`
--   and `length(γ)` — in particular not on `Q`, not on `ε`, and not on the curve `γ` beyond its
--   length. The upper bound comes from discarding the second argument of each of the `m` minima in
--   `\noderef{psi}`'s defining sum, so no `infDist` estimate enters at all.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiUniformBound.lean#L10-L40
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiUniformBound.lean#L10-L40

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PsiUniformBound
set_option autoImplicit false

theorem PsiUniformBound {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psi m Q ε C γ ∧
      psi m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by sorry
