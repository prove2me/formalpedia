-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:55.646941+00:00
-- url     : https://prove2.me/theorems/0ae81ec1-9666-4f5f-b1a2-fb0e4e69fef4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper eq unip Mat 8f17e87357aa: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper eq unip Mat 8f17e87357aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper eq unip Mat 8f17e87357aa construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper eq unip Mat 8f17e87357aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L32-L68

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa {H G : Matrix ι ι ℂ} {X W₀ : ι → ℂ} (hU : Gᴴ * H * G = H)
    (hX : G *ᵥ X = X) (hz : ∀ z, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, G *ᵥ z = z + c • X)
    (hXW : star X ⬝ᵥ (H *ᵥ W₀) = 1) (hWX : star W₀ ⬝ᵥ (H *ᵥ X) = 1) :
    G = unipMat H X W₀ (G *ᵥ W₀ - W₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCoordProper».«eq_unipMat» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa
