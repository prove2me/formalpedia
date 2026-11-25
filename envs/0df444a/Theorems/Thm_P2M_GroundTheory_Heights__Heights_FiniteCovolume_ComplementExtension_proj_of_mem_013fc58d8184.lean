-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_of_mem_013fc58d8184
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_of_mem_013fc58d8184
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:23.102525+00:00
-- url     : https://prove2.me/theorems/d1b58287-9ef0-5b40-b07a-4a5186ac17b1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj of mem 013fc58d8184: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj of mem 013fc58d8184
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj of mem 013fc58d8184 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj of mem 013fc58d8184 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L98-L103

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_of_mem_013fc58d8184 (hp : IsHyperbolicPair h v w) (x : hypComplement h v w) :
    proj hp (x : W) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«proj_of_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_of_mem_013fc58d8184
