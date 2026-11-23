-- Prove2me | Theorems.Thm_PI_PoincareSeriesInner_W_poinc_split
-- name    : PI.PoincareSeriesInner.W.poinc_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:29.487539+00:00
-- url     : https://prove2.me/theorems/d6a8b9d4-cadc-4b18-b32c-c554044feefe
-- title:
--   W: poinc split
-- statement:
--   The W construction uses the poinc split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean#L48-L58

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

theorem PI.PoincareSeriesInner.W.poinc_split {G : Type*} [Group G] (E : Set G) (v : Fin 4 → G → ℝ≥0∞) (f : G → ℂ)
    (hf : ∀ x, f x = ∑ k, cf k * ((v k x).toReal : ℂ))
    (hv : ∀ k x, ∑' δ : E, v k ((δ : G) * x) ≠ ⊤) (x : G) :
    poinc E f x = ∑ k, cf k * (((∑' δ : E, v k ((δ : G) * x))).toReal : ℂ) := by sorry
