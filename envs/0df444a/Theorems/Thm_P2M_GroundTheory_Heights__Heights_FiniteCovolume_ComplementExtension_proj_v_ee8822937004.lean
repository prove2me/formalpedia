-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_v_ee8822937004
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_v_ee8822937004
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:16.326462+00:00
-- url     : https://prove2.me/theorems/c6dd37d0-8135-4f5a-8aea-cb544cf7e90a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj v ee8822937004: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj v ee8822937004
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj v ee8822937004 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension proj v ee8822937004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L105-L108

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_v_ee8822937004 (hp : IsHyperbolicPair h v w) : proj hp v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«proj_v» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_v_ee8822937004
