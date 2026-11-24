-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:37.148478+00:00
-- url     : https://prove2.me/theorems/04e3aac0-eaa3-4d8c-991b-064f73baac08
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb alt eq sum 69324f4b2849: P2 M Ground Theory Heights  Heights Rest Terms Comb alt eq sum 69324f4b2849
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb alt eq sum 69324f4b2849 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb alt eq sum 69324f4b2849 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L75-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849 (v : Fin m → ℕ) :
    alt v = ∑ σ : Perm (Fin m), (Perm.sign σ : ℤ) • monomial (ex (v ∘ σ.symm)) (1 : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«alt_eq_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
