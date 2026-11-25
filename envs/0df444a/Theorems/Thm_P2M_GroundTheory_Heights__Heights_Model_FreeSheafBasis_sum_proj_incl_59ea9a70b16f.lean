-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:07.41983+00:00
-- url     : https://prove2.me/theorems/b5c42806-d30c-46cf-b99f-71a6c6da57d5
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj incl 59ea9a70b16f: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj incl 59ea9a70b16f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj incl 59ea9a70b16f construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj incl 59ea9a70b16f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L49-L50

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

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f : ∑ j, proj Y n j ≫ incl Y n j = 𝟙 (freeModule Y n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«sum_proj_incl» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f
