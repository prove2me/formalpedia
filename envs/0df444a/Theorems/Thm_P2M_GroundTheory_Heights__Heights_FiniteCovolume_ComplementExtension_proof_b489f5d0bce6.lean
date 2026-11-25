-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:48:59.870319+00:00
-- url     : https://prove2.me/theorems/dbe987f5-a829-50d0-bbd5-7270776bf7db
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proof b489f5d0bce6: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proof b489f5d0bce6
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proof b489f5d0bce6 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proof b489f5d0bce6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L115-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L115-L144

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6 (h : HermitianForm F E W) : ComplementExtension.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
