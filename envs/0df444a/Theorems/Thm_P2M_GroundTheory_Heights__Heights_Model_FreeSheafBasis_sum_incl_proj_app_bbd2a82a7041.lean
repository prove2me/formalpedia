-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:12.421168+00:00
-- url     : https://prove2.me/theorems/d1c8d5f7-6499-49c0-9ca3-79d6ccb5fb7d
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum incl proj app bbd2a82a7041: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum incl proj app bbd2a82a7041
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum incl proj app bbd2a82a7041 construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum incl proj app bbd2a82a7041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L71-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable (Y : Scheme.{u}) (n : ℕ)
variable {Y n}

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041 (V : Y.Opens) (m : Γ(freeModule Y n, V)) :
    ∑ j, ((incl Y n j).app V).hom (((proj Y n j).app V).hom m) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«sum_incl_proj_app» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041
