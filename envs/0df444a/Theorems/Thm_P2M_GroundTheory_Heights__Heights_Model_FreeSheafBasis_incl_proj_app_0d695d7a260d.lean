-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:57.579936+00:00
-- url     : https://prove2.me/theorems/0a2952ec-58c8-4c34-afc1-28ffcb12cab9
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj app 0d695d7a260d: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj app 0d695d7a260d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj app 0d695d7a260d construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis incl proj app 0d695d7a260d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L65-L69

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

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d (V : Y.Opens) (i j : Fin n) (r : Γ(Y, V)) :
    ((proj Y n j).app V).hom (((incl Y n i).app V).hom r) = if i = j then r else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«incl_proj_app» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d
