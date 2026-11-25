-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58
-- name    : P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:53.849504+00:00
-- url     : https://prove2.me/theorems/8c78cc69-2188-5405-9779-5f7c83fd208c
-- title:
--   P2 M Ground Theory Heights  Heights Cone Map Area Formula lintegral cone prod 6b346da01c58: P2 M Ground Theory Heights  Heights Cone Map Area Formula lintegral cone prod 6b346da01c58
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Map Area Formula lintegral cone prod 6b346da01c58 construction uses the P2 M Ground Theory Heights  Heights Cone Map Area Formula lintegral cone prod 6b346da01c58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L182-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMapAreaOne.lean#L182-L193

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

theorem P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58 {e : ℕ} {D : Set (Fin e → ℂ)} (G : (Fin e → ℂ) × ℂ → ℝ≥0∞)
    (hG : AEMeasurable G ((volume.restrict D).prod volume)) :
    ∫⁻ q in {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0}, G q = ∫⁻ x in D, ∫⁻ t, G (x, t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMapAreaFormula».«lintegral_cone_prod» := P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58
