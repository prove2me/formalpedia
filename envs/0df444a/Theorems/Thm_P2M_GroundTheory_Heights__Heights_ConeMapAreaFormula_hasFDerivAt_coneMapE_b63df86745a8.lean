-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:31:50.518865+00:00
-- url     : https://prove2.me/theorems/7d80d70a-6a11-414c-9aa1-4c6408f2d65b
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula has FDeriv At cone Map E b63df86745a8: P2 M Ground Theory Heights  Heights Cone Map Area Formula has FDeriv At cone Map E b63df86745a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula has FDeriv At cone Map E b63df86745a8 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula has FDeriv At cone Map E b63df86745a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L111-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L111-L122

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8 {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    HasFDerivAt (coneMapE v)
      (p 0 • ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
          ((fderiv ℂ v (tailL e p)).comp (tailL e))) +
        (EuclideanSpace.proj (0 : Fin (e + 1)) :
          EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).smulRight (WithLp.toLp 2 (v (tailL e p)))) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«hasFDerivAt_coneMapE» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8
