-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:27.90802+00:00
-- url     : https://prove2.me/theorems/02c3f4e9-9641-487c-b77d-cc21baf56105
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj 2dae232b015b: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj 2dae232b015b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj 2dae232b015b construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj 2dae232b015b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L45-L47

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

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b (i j : Fin n) :
    incl Y n i ≫ proj Y n j = if i = j then 𝟙 (structureModule Y) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«incl_proj» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b
