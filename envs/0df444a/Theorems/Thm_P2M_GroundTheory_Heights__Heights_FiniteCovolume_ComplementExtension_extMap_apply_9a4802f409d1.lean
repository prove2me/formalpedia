-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_apply_9a4802f409d1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_apply_9a4802f409d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:06.027239+00:00
-- url     : https://prove2.me/theorems/8c437e32-6d5e-5016-bf68-10222e50d583
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map apply 9a4802f409d1: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map apply 9a4802f409d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map apply 9a4802f409d1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map apply 9a4802f409d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L60-L62

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_apply_9a4802f409d1 (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    extMap hp m x = h.toSesq w x • v + (m (proj hp x) : W) + h.toSesq v x • w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«extMap_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_apply_9a4802f409d1
