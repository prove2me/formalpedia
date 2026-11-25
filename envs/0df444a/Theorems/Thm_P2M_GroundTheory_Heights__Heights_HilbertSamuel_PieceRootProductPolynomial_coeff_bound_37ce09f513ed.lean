-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:15.674081+00:00
-- url     : https://prove2.me/theorems/305f5860-9aba-4d2d-9859-0570bd2f1aff
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff bound 37ce09f513ed: P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff bound
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff bound 37ce09f513ed construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff bound 37ce09f513ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceRootProductPolynomial.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceRootProductPolynomial.lean#L12-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceRootProductPolynomial
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
open MvPolynomial Matrix

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed {ι : Type*} (s : Finset ι) (r : ι → ℂ) (B : ℝ)
    (hB : ∀ x ∈ s, ‖r x‖ ≤ B) (i : ℕ) :
    ‖(∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).coeff i‖ ≤ B ^ (s.card - i) * (s.card.choose i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PieceRootProductPolynomial».«coeff_bound» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed
