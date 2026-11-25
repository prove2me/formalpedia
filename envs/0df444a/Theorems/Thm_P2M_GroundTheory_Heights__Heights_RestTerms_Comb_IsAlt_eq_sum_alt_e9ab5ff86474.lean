-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_sum_alt_e9ab5ff86474
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_sum_alt_e9ab5ff86474
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:52.717795+00:00
-- url     : https://prove2.me/theorems/98a88d33-f2d7-4090-b561-d95e7f98c875
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq sum alt e9ab5ff86474: P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq sum alt e9ab5ff86474
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq sum alt e9ab5ff86474 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq sum alt e9ab5ff86474 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L234-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L234-L256

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_sum_alt_e9ab5ff86474 {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) :
    P = ∑ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)), coeff d P • alt (⇑d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«IsAlt».«eq_sum_alt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_sum_alt_e9ab5ff86474
