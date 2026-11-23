-- Prove2me | Theorems.Thm_PI_PoincareSeriesInner_W_toReal_int
-- name    : PI.PoincareSeriesInner.W.toReal_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:52.562319+00:00
-- url     : https://prove2.me/theorems/b1af9ca6-b70e-4d5c-80e2-602a7b523c3b
-- title:
--   W: to Real int
-- statement:
--   The W construction uses the to Real int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L41-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.PoincareSeriesInner PI.PoincareSeriesInner.W
universe u

theorem PI.PoincareSeriesInner.W.toReal_int {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hfin : ∫⁻ x, f x ∂ν ≠ ⊤) (hpt : ∀ x, f x ≠ ⊤) :
    Integrable (fun x => ((f x).toReal : ℂ)) ν ∧
      ∫ x, ((f x).toReal : ℂ) ∂ν = (((∫⁻ x, f x ∂ν).toReal : ℝ) : ℂ) := by sorry
