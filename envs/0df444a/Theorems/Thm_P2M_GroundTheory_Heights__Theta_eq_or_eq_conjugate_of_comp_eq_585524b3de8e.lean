-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e
-- name    : P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:14.084852+00:00
-- url     : https://prove2.me/theorems/7b2c1059-d1c8-590a-8667-d273f7f2e8ae
-- title:
--   P2 M Ground Theory Heights  Theta eq or eq conjugate of comp eq 585524b3de8e: P2 M Ground Theory Heights  Theta eq or eq conjugate of comp eq 585524b3de8e
-- statement:
--   The P2 M Ground Theory Heights  Theta eq or eq conjugate of comp eq 585524b3de8e construction uses the P2 M Ground Theory Heights  Theta eq or eq conjugate of comp eq 585524b3de8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L93-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L93-L118

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

theorem P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e (φ ψ : E →+* ℂ)
    (h : φ.comp (algebraMap F E) = ψ.comp (algebraMap F E)) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«eq_or_eq_conjugate_of_comp_eq» := P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e
