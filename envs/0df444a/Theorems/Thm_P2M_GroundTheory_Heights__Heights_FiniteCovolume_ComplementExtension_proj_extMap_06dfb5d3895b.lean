-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_extMap_06dfb5d3895b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_extMap_06dfb5d3895b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:58.726259+00:00
-- url     : https://prove2.me/theorems/286ab062-a986-5234-9b85-1c30dd13fa8d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj ext Map 06dfb5d3895b: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj ext Map 06dfb5d3895b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj ext Map 06dfb5d3895b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj ext Map 06dfb5d3895b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L78-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_extMap_06dfb5d3895b (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    proj hp (extMap hp m x) = m (proj hp x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«proj_extMap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_extMap_06dfb5d3895b
