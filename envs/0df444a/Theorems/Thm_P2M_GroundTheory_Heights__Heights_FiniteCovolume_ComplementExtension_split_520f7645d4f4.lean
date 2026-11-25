-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_split_520f7645d4f4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_split_520f7645d4f4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:16.847995+00:00
-- url     : https://prove2.me/theorems/440cfb9b-f0b6-5925-890a-ba594aa9c3aa
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension split 520f7645d4f4: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension split 520f7645d4f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension split 520f7645d4f4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension split 520f7645d4f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L40-L42

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_split_520f7645d4f4 (hp : IsHyperbolicPair h v w) (x : W) :
    h.toSesq w x • v + (proj hp x : W) + h.toSesq v x • w = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«split» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_split_520f7645d4f4
