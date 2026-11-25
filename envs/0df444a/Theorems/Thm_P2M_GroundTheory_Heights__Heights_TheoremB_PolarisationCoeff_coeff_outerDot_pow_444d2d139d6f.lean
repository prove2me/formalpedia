-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:10.942831+00:00
-- url     : https://prove2.me/theorems/6a56e3f6-b926-4a55-ad86-d538a0439655
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff outer Dot pow 444d2d139d6f: P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff outer Dot pow 444d2d139d6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff outer Dot pow 444d2d139d6f construction uses the P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff outer Dot pow 444d2d139d6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L27-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L27-L58

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f {σ R : Type*} [CommRing R] [Fintype σ] (n : ℕ) (m : σ →₀ ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    coeff m ((outerDot σ R) ^ n) = (Nat.multinomial univ m : MvPolynomial σ R) * monomial m 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«PolarisationCoeff».«coeff_outerDot_pow» := P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_outerDot_pow_444d2d139d6f
