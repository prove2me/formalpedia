-- Prove2me | Theorems.Thm_PsiMeasurable
-- name    : PsiMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:30.465193+00:00
-- url     : https://prove2.me/theorems/45b91836-20ac-5b7d-a1b0-53df6df8d5ec
-- title:
--   Psi Measurable: Psi Measurable
-- statement:
--   `ψ_{m,Q,ε,C}` (`psi`) is measurable as a function of `γ : Θ(E)`, with `Θ(E)` carrying the
--   evaluation `σ`-algebra of `CurveMeasurableSpace`. Needed because `PsiVanishes` states an
--   inequality between Bochner integrals of `psi`/`psiTilde` against a measure on `Θ(E)`, and Lean's
--   Bochner integral of a non-measurable (hence non-integrable) function is definitionally `0`: without
--   this fact in hand, such an inequality would be satisfiable by a `ψ` that is not measurable at all,
--   the same shape of vacuity `psi_zero_at_m_zero` records at `m = 0`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiMeasurable.lean#L14-L31
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiMeasurable.lean#L14-L31

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_PsiMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable

set_option autoImplicit false
open MeasureTheory

theorem PsiMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psi m Q ε C γ) := by sorry
