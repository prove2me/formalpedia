-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0
-- name    : P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:52.580127+00:00
-- url     : https://prove2.me/theorems/1139deea-3a61-4228-9d17-b9bddab8af4f
-- title:
--   P2 M Ground Theory Heights  Heights aemeasurable cone Term 4ac5814534a0: P2 M Ground Theory Heights  Heights aemeasurable cone Term 4ac5814534a0
-- statement:
--   The P2 M Ground Theory Heights  Heights aemeasurable cone Term 4ac5814534a0 construction uses the P2 M Ground Theory Heights  Heights aemeasurable cone Term 4ac5814534a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L43-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L43-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal

theorem P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0 {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aemeasurable_coneTerm» := P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0
