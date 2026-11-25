-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f
-- name    : P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:50.280448+00:00
-- url     : https://prove2.me/theorems/00ffd217-3357-4092-ab6b-0087e2849eca
-- title:
--   P2 M Ground Theory Heights  Heights graph Pt injective c1602eb4686f: P2 M Ground Theory Heights  Heights graph Pt injective c1602eb4686f
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Pt injective c1602eb4686f construction uses the P2 M Ground Theory Heights  Heights graph Pt injective c1602eb4686f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L16-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphPt_injective» := P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f
