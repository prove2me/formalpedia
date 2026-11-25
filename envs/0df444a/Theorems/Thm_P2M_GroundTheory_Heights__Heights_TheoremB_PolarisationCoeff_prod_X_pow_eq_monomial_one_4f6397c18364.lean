-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:45.02486+00:00
-- url     : https://prove2.me/theorems/109d2e9e-4b97-52cd-87fd-eab033787a8b
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff prod X pow eq monomial one 4f6397c18364: P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff prod X pow eq monomial one 4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff prod X pow eq monomial one 4f6397c18364 construction uses the P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff prod X pow eq monomial one 4f6397c18364 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364 {σ S : Type*} [CommSemiring S] [Fintype σ] (K : σ →₀ ℕ) :
    ∏ v, (X v : MvPolynomial σ S) ^ K v = monomial K 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«PolarisationCoeff».«prod_X_pow_eq_monomial_one» := P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_prod_X_pow_eq_monomial_one_4f6397c18364
