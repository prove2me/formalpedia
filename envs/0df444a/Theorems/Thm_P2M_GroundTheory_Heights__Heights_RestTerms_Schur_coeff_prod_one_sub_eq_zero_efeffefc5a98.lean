-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:58.549813+00:00
-- url     : https://prove2.me/theorems/84063e44-913e-5598-bca7-2721be2b9a0e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod one sub eq zero efeffefc5a98: P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod one sub eq zero efeffefc5a98
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod one sub eq zero efeffefc5a98 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod one sub eq zero efeffefc5a98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L62-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98 {ι : Type*} [DecidableEq ι] (a : ι → R) (s : Finset ι) :
    ∀ c : ℕ, s.card < c →
      PowerSeries.coeff c (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«coeff_prod_one_sub_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_one_sub_eq_zero_efeffefc5a98
