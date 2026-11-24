-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:15.856795+00:00
-- url     : https://prove2.me/theorems/787773af-4252-4fb9-a17d-a1e80c606f76
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf mul psum 0f698be248eb: P2 M Ground Theory Heights  Heights Rest Terms Comb cf mul psum 0f698be248eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf mul psum 0f698be248eb construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf mul psum 0f698be248eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L154-L171

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb (l : Fin m → ℕ) (A : MvPolynomial (Fin m) ℚ) (q : ℕ) :
    cf l (A * psum (Fin m) ℚ q) =
      ∑ i, if q ≤ l i then cf (Function.update l i (l i - q)) A else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_mul_psum» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb
