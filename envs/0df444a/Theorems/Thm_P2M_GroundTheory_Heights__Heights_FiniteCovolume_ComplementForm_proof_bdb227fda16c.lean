-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:48.967994+00:00
-- url     : https://prove2.me/theorems/2c479269-6b24-4897-9942-137ef347ad2f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Form proof bdb227fda16c: P2 M Ground Theory Heights  Heights Finite Covolume Complement Form proof bdb227fda16c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Form proof bdb227fda16c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Form proof bdb227fda16c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementForm.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementForm.lean#L94-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c (h : HermitianForm F E W) : ComplementForm.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementForm».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c
