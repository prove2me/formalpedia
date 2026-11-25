-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:46.480796+00:00
-- url     : https://prove2.me/theorems/187a8dce-6204-4394-b62c-8b6b2bea7736
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On injective of app 69a59355bfc7: P2 M Ground Theory Heights  Heights Model pull Section On injective of app 69a59355bfc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On injective of app 69a59355bfc7 construction uses the P2 M Ground Theory Heights  Heights Model pull Section On injective of app 69a59355bfc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L28-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericPullInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7 (hPB : PullbackBasis.Statement.{0}) {T Z : Scheme.{0}}
    (g : T ⟶ Z) (M : Z.Modules) (hM : IsVectorBundle M) (V : Z.Opens)
    (hg : ∀ W : Z.Opens, W ≤ V → Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_injective_of_app» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7
