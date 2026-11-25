-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:42.789627+00:00
-- url     : https://prove2.me/theorems/ac5fa55b-63d0-4c91-a97e-efbdd3b253e4
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On injective of basis of app 430ada2a134c: P2 M Ground Theory Heights  Heights Model pull Section On injective of basis of app 430ada2a134c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On injective of basis of app 430ada2a134c construction uses the P2 M Ground Theory Heights  Heights Model pull Section On injective of basis of app 430ada2a134c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L13-L26

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c (hPB : PullbackBasis.Statement.{0})
    {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules) {W : Z.Opens} {n : ℕ} {t : Fin n → Γ(M, W)}
    (ht : IsBasisOn M W t) (hg : Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_injective_of_basis_of_app» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c
