-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_comp_c4909a10b405
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_comp_c4909a10b405
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:44.194478+00:00
-- url     : https://prove2.me/theorems/fd905954-ffae-40d1-b9ee-46248a0d6cf5
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map comp c4909a10b405: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map comp c4909a10b405
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map comp c4909a10b405 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map comp c4909a10b405 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L85-L91

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_comp_c4909a10b405 (hp : IsHyperbolicPair h v w)
    (m m' : hypComplement h v w →ₗ[E] hypComplement h v w) :
    extMap hp m ∘ₗ extMap hp m' = extMap hp (m ∘ₗ m') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«extMap_comp» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_comp_c4909a10b405
