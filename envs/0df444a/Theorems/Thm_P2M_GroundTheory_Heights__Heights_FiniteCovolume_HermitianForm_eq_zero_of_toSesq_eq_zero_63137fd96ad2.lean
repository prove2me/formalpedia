-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermitianForm_eq_zero_of_toSesq_eq_zero_63137fd96ad2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermitianForm_eq_zero_of_toSesq_eq_zero_63137fd96ad2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:40.262274+00:00
-- url     : https://prove2.me/theorems/cf7339c3-73c8-53df-9cba-ee9870ba9120
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hermitian Form eq zero of to Sesq eq zero 63137fd96ad2: P2 M Ground Theory Heights  Heights Finite Covolume Hermitian Form eq zero of to Sesq eq zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hermitian Form eq zero of to Sesq eq zero 63137fd96ad2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hermitian Form eq zero of to Sesq eq zero 63137fd96ad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTraceHermNondegenerate.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTraceHermNondegenerate.lean#L14-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTraceHermNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermitianForm_eq_zero_of_toSesq_eq_zero_63137fd96ad2 (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HermitianForm».«eq_zero_of_toSesq_eq_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermitianForm_eq_zero_of_toSesq_eq_zero_63137fd96ad2
