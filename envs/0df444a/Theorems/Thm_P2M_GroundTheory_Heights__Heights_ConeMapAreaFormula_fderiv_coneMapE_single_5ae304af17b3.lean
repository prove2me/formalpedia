-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:57.778249+00:00
-- url     : https://prove2.me/theorems/6c5227d3-0722-4cc3-a213-a339c124fedc
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula fderiv cone Map E single 5ae304af17b3: P2 M Ground Theory Heights  Heights Cone Map Area Formula fderiv cone Map E single 5ae304af17b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula fderiv cone Map E single 5ae304af17b3 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula fderiv cone Map E single 5ae304af17b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L124-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L124-L137

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3 {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) (a : Fin (e + 1)) :
    fderiv ℂ (coneMapE v) p (EuclideanSpace.single a 1) =
      (Fin.cons 1 (fun _ => p 0) : Fin (e + 1) → ℂ) a • WithLp.toLp 2 (gramVecs v (tailL e p) a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«fderiv_coneMapE_single» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_fderiv_coneMapE_single_5ae304af17b3
