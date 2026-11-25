-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:18.31782+00:00
-- url     : https://prove2.me/theorems/e5b3ecdc-433e-427b-89b0-dfaf1cbb6957
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj C   11ca3dfecaad: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj C   11ca3dfecaad
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj C   11ca3dfecaad construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis sum proj C   11ca3dfecaad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L28-L33

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
variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad :
    ∑ j : Fin n, projC A n j ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up j) = 𝟙 _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«sum_projC_ι» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad
