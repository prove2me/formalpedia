-- Prove2me | Theorems.Thm_PsiTildeUniformBound
-- name    : PsiTildeUniformBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:35.406383+00:00
-- url     : https://prove2.me/theorems/fd1deaa9-1e34-420b-b1b4-81c8e7e7fafc
-- title:
--   Psi Tilde Uniform Bound: Psi Tilde Uniform Bound
-- statement:
--   The a priori two-sided bound on `ψ̃_{m,Q,ε,C}` used for integrability, companion to
--   `\noderef{PsiUniformBound}`: for `m ≥ 1`, `ε ≥ 0` and `C ≥ 0`, the quantity
--   `ψ̃_{m,Q,ε,C}(γ)` of `\noderef{psiTilde}` is nonnegative and bounded above by the same
--   expression `2C²·length(γ) + 2C²·length(γ)²/m`, depending only on `m`, `C` and `length(γ)`.
--   The upper bound comes from discarding the second argument of each of the `m` minima in
--   `\noderef{psiTilde}`'s defining sum, so no `infDist` estimate enters at all.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiTildeUniformBound.lean#L10-L39
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiTildeUniformBound.lean#L10-L39

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiTildeUniformBound
set_option autoImplicit false

theorem PsiTildeUniformBound {E : Type*} [MetricSpace E] (m : ℕ) (hm : 0 < m) (Q : Finset E)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (γ : Curve E) :
    0 ≤ psiTilde m Q ε C γ ∧
      psiTilde m Q ε C γ ≤ 2 * C ^ 2 * γ.len + 2 * C ^ 2 * γ.len ^ 2 / (m : ℝ) := by sorry
