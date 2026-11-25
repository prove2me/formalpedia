-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:46.027094+00:00
-- url     : https://prove2.me/theorems/d230ea96-8e8d-4230-811c-9e1469e93225
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula area Jacobian cone Map E d9a776937d95: P2 M Ground Theory Heights  Heights Cone Map Area Formula area Jacobian cone Map E d9a776937d95
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula area Jacobian cone Map E d9a776937d95 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula area Jacobian cone Map E d9a776937d95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L143-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L143-L176

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95 {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    areaJacobian ((fderiv ℂ (coneMapE v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) = ‖p 0‖ ^ (2 * e) * gramVol v (tailL e p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«areaJacobian_coneMapE» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95
