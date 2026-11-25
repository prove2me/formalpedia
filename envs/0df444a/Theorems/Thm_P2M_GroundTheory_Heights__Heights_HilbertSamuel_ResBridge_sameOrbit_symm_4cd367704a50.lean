-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_sameOrbit_symm_4cd367704a50
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_sameOrbit_symm_4cd367704a50
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:19:48.84567+00:00
-- url     : https://prove2.me/theorems/3d0941b6-efba-4324-b369-c47c8ccbeb1c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge same Orbit symm 4cd367704a50: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge same Orbit symm 4cd367704a50
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge same Orbit symm 4cd367704a50 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge same Orbit symm 4cd367704a50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L34-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_sameOrbit_symm_4cd367704a50 {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z') :
    ReciprocityTheory.AnForm.R.SameOrbit z' z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«sameOrbit_symm» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_sameOrbit_symm_4cd367704a50
