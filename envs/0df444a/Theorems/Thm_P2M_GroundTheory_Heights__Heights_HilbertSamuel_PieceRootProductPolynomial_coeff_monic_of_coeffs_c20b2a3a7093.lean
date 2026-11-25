-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:53.125216+00:00
-- url     : https://prove2.me/theorems/093e0e6d-79cd-5b9d-99c0-491c9a74a9c6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff monic of coeffs c20b2a3a7093: P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial co
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff monic of coeffs c20b2a3a7093 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Piece Root Product Polynomial coeff monic of coeffs c20b2a3a7093 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceRootProductPolynomial.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceRootProductPolynomial.lean#L34-L51

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093 {R : Type*} [CommRing R] (k : ℕ) (p : ℕ → R)
    (i : ℕ) :
    (Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)).coeff i =
      if i < k then p i else if i = k then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PieceRootProductPolynomial».«coeff_monic_of_coeffs» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_monic_of_coeffs_c20b2a3a7093
