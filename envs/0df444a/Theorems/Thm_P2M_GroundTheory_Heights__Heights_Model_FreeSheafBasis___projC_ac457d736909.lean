-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:47.497129+00:00
-- url     : https://prove2.me/theorems/6409cca1-6150-4c71-b8e3-56899e8b1887
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis   proj C ac457d736909: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis   proj C ac457d736909
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis   proj C ac457d736909 construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis   proj C ac457d736909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean#L23-L26

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

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909 (i j : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up i) ≫ projC A n j =
      if i = j then 𝟙 A else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«ι_projC» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909
