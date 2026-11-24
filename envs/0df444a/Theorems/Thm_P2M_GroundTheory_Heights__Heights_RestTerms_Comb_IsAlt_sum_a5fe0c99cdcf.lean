-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:26.814848+00:00
-- url     : https://prove2.me/theorems/f3e256ae-0708-4447-96be-6312e6705ab0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt sum a5fe0c99cdcf: P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt sum a5fe0c99cdcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt sum a5fe0c99cdcf construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt sum a5fe0c99cdcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L189-L196

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Fin m) ℚ}
    (hP : ∀ i ∈ s, IsAlt (P i)) : IsAlt (∑ i ∈ s, P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«IsAlt».«sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
