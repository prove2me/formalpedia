-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_apply_ad92f62b9ffa
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_apply_ad92f62b9ffa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:02.164214+00:00
-- url     : https://prove2.me/theorems/ef8f2db7-5e5f-5549-89c5-7e286986bad4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj apply ad92f62b9ffa: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj apply ad92f62b9ffa
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj apply ad92f62b9ffa construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj apply ad92f62b9ffa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L37-L38

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_apply_ad92f62b9ffa (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«proj_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_apply_ad92f62b9ffa
