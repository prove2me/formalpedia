-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:12.805915+00:00
-- url     : https://prove2.me/theorems/9f8d0228-2e8f-4b16-9e6a-9a28b4d2ca08
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula aemeasurable cone Integrand 23ef9853180b: P2 M Ground Theory Heights  Heights Cone Map Area Formula aemeasurable cone Integrand 23ef9853180b
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula aemeasurable cone Integrand 23ef9853180b construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula aemeasurable cone Integrand 23ef9853180b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L195-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L195-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
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
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open GroundTheory.Heights₂.Heights.ConeMapAreaFormula

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b {e n : ℕ} {U D : Set (Fin e → ℂ)}
    {v : (Fin e → ℂ) → (Fin n → ℂ)} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hD : MeasurableSet D)
    (hDU : D ⊆ U) (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (coneIntegrand v F) ((volume.restrict D).prod volume) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«aemeasurable_coneIntegrand» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b
