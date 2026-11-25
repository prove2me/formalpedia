-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:02.790804+00:00
-- url     : https://prove2.me/theorems/08cd37a3-d52a-4dbe-b79b-b7e5aa66e2d4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv monomial staircase eq c1973ddcf09b: P2 M Ground Theory Heights  Heights Rest Terms Coinv monomial staircase eq c1973ddcf09b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv monomial staircase eq c1973ddcf09b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv monomial staircase eq c1973ddcf09b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvariantTopDegree.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvariantTopDegree.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvariantTopDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b (f N : ℕ) :
    (monomial (Coinv.staircase f N) (1 : ℚ) : RootRing f N) =
      ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«monomial_staircase_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b
