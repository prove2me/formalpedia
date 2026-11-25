-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:39.304499+00:00
-- url     : https://prove2.me/theorems/3ae6df66-88fd-5f94-802b-22895e13d8db
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff polar Poly d5a631653db6: P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff polar Poly d5a631653db6
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff polar Poly d5a631653db6 construction uses the P2 M Ground Theory Heights  Heights Theorem B Polarisation Coeff coeff polar Poly d5a631653db6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationCoeff.lean#L15-L25

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6 {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (m : σ →₀ ℕ) :
    coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«PolarisationCoeff».«coeff_polarPoly» := P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6
