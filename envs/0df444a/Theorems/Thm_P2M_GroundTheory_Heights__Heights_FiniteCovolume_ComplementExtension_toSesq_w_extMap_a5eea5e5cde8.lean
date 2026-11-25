-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_w_extMap_a5eea5e5cde8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_w_extMap_a5eea5e5cde8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:48.337704+00:00
-- url     : https://prove2.me/theorems/a62826cf-43c1-4807-ac2d-bdaafb41f1b9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq w ext Map a5eea5e5cde8: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq w ext Map a5ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq w ext Map a5eea5e5cde8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq w ext Map a5eea5e5cde8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L64-L69

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_w_extMap_a5eea5e5cde8 (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq w (extMap hp m x) = h.toSesq w x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«toSesq_w_extMap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_w_extMap_a5eea5e5cde8
