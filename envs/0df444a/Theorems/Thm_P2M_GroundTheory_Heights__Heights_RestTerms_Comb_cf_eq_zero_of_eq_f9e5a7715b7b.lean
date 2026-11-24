-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:28.634994+00:00
-- url     : https://prove2.me/theorems/d7212d67-8818-4011-bb12-3429fe153c02
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf eq zero of eq f9e5a7715b7b: P2 M Ground Theory Heights  Heights Rest Terms Comb cf eq zero of eq f9e5a7715b7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf eq zero of eq f9e5a7715b7b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf eq zero of eq f9e5a7715b7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L60-L73

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) {v : Fin m → ℕ} {i j : Fin m}
    (hij : i ≠ j) (h : v i = v j) : cf v P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_eq_zero_of_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
