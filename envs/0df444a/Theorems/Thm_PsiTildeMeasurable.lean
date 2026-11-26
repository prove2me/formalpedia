-- Prove2me | Theorems.Thm_PsiTildeMeasurable
-- name    : PsiTildeMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:49.87115+00:00
-- url     : https://prove2.me/theorems/8c8cedc4-f2fe-41f6-8b77-fe7a2e1b70a5
-- title:
--   Psi Tilde Measurable: Psi Tilde Measurable
-- statement:
--   `ψ̃_{m,Q,ε,C}` (`psiTilde`) is measurable as a function of `γ : Θ(E)`, with `Θ(E)` carrying
--   the evaluation `σ`-algebra of `CurveMeasurableSpace`. Needed for the same reason as
--   `PsiMeasurable`: `PsiVanishes` states an inequality between Bochner integrals of `psi`/`psiTilde`
--   against a measure on `Θ(E)`, and Lean's Bochner integral of a non-measurable (hence
--   non-integrable) function is definitionally `0`, so without this fact the inequality would be
--   satisfiable by a `ψ̃` that is not measurable at all.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiTildeMeasurable.lean#L14-L30
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiTildeMeasurable.lean#L14-L30

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable

set_option autoImplicit false
open MeasureTheory

theorem PsiTildeMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (Q : Finset E) (ε C : ℝ) :
    Measurable (fun γ : Curve E => psiTilde m Q ε C γ) := by sorry
