-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_split_fa8429a6b377
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_split_fa8429a6b377
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:47.194168+00:00
-- url     : https://prove2.me/theorems/ebd48ff9-ef97-5733-9ff1-76aa44a56639
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq split fa8429a6b377: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq split fa8429a6b377
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq split fa8429a6b377 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq split fa8429a6b377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L44-L53

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_split_fa8429a6b377 (hp : IsHyperbolicPair h v w) (a b a' b' : E) (z z' : hypComplement h v w) :
    h.toSesq (a • v + (z : W) + b • w) (a' • v + (z' : W) + b' • w) =
      conjHom F E a * b' + conjHom F E b * a' + h.toSesq z z' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«toSesq_split» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_split_fa8429a6b377
