-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:59.625704+00:00
-- url     : https://prove2.me/theorems/18f67e3e-6771-589e-853c-7d5442db0009
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel coeff finset prod differentiable At 085abbefa066: P2 M Ground Theory Heights  Heights Hilbert Samuel coeff finset prod differentiable At 085abbefa066
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel coeff finset prod differentiable At 085abbefa066 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel coeff finset prod differentiable At 085abbefa066 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceCoefficientsHolomorphic.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceCoefficientsHolomorphic.lean#L9-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceCoefficientsHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066 {d : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → (Fin d → ℂ) → Polynomial ℂ) (y₀ : Fin d → ℂ)
    (hP : ∀ i ∈ S, ∀ k, DifferentiableAt ℂ (fun y => (P i y).coeff k) y₀) :
    ∀ k, DifferentiableAt ℂ (fun y => (∏ i ∈ S, P i y).coeff k) y₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«coeff_finset_prod_differentiableAt» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066
