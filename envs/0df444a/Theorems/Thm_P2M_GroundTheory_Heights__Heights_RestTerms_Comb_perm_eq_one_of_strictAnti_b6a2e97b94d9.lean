-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:06.975487+00:00
-- url     : https://prove2.me/theorems/2f75c308-8ce6-45f8-9e13-1ac20c451cf2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb perm eq one of strict Anti b6a2e97b94d9: P2 M Ground Theory Heights  Heights Rest Terms Comb perm eq one of strict Anti b6a2e97b94d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb perm eq one of strict Anti b6a2e97b94d9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb perm eq one of strict Anti b6a2e97b94d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L110-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L110-L129

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9 {v : Fin m → ℕ} (hv : StrictAnti v) (σ : Perm (Fin m))
    (h : StrictAnti (v ∘ σ)) : σ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«perm_eq_one_of_strictAnti» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9
