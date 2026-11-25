-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_gramVol_eq_967d5336b167
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_gramVol_eq_967d5336b167
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:03.932391+00:00
-- url     : https://prove2.me/theorems/54250e88-903c-5abe-9269-1ccd7fdab9ae
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula gram Vol eq 967d5336b167: P2 M Ground Theory Heights  Heights Cone Map Area Formula gram Vol eq 967d5336b167
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula gram Vol eq 967d5336b167 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula gram Vol eq 967d5336b167 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L106-L109

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_gramVol_eq_967d5336b167 {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y =
      (Matrix.det (Matrix.of fun a b => ∑ i, star (gramVecs v y a i) * gramVecs v y b i)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«gramVol_eq» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_gramVol_eq_967d5336b167
