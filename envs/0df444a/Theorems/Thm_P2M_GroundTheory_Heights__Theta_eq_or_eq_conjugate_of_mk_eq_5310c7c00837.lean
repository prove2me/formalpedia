-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_mk_eq_5310c7c00837
-- name    : P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_mk_eq_5310c7c00837
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:03.539724+00:00
-- url     : https://prove2.me/theorems/ab22bdf7-d874-58e2-aa00-76fccb42308d
-- title:
--   P2 M Ground Theory Heights  Theta eq or eq conjugate of mk eq 5310c7c00837: P2 M Ground Theory Heights  Theta eq or eq conjugate of mk eq 5310c7c00837
-- statement:
--   The P2 M Ground Theory Heights  Theta eq or eq conjugate of mk eq 5310c7c00837 construction uses the P2 M Ground Theory Heights  Theta eq or eq conjugate of mk eq 5310c7c00837 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L120-L129

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)

theorem P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_mk_eq_5310c7c00837 (φ ψ : E →+* ℂ)
    (h : InfinitePlace.mk (φ.comp (algebraMap F E)) = InfinitePlace.mk (ψ.comp (algebraMap F E))) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«eq_or_eq_conjugate_of_mk_eq» := P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_mk_eq_5310c7c00837
