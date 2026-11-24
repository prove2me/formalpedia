-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:06.721659+00:00
-- url     : https://prove2.me/theorems/fe944661-f867-4807-be70-f7626285b0e1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf sum 377f06929651: P2 M Ground Theory Heights  Heights Rest Terms Comb cf sum 377f06929651
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf sum 377f06929651 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf sum 377f06929651 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L97-L98

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651 {ι : Type*} (s : Finset ι) (v : Fin m → ℕ) (P : ι → MvPolynomial (Fin m) ℚ) :
    cf v (∑ i ∈ s, P i) = ∑ i ∈ s, cf v (P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651
