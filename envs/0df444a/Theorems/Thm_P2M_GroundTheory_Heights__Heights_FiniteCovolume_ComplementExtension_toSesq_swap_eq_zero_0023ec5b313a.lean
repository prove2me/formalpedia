-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_swap_eq_zero_0023ec5b313a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_swap_eq_zero_0023ec5b313a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:50:39.215145+00:00
-- url     : https://prove2.me/theorems/69e505a0-3d84-462d-a11f-f57a6d5390ba
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq swap eq zero 0023ec5b313a: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq swap eq zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq swap eq zero 0023ec5b313a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq swap eq zero 0023ec5b313a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L25-L26

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_swap_eq_zero_0023ec5b313a {u z : W} (hz : h.toSesq u z = 0) : h.toSesq z u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«toSesq_swap_eq_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_swap_eq_zero_0023ec5b313a
