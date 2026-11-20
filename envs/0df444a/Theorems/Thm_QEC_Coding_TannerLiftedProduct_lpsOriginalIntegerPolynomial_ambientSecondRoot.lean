-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_ambientSecondRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_ambientSecondRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:36:22.300188+00:00
-- url     : https://prove2.me/theorems/3f0aa7bb-88b2-4136-9523-2a87c32012e7
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial ambient Second Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial ambient Second Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L149-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L149-L163

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_ambientSecondRoot
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
        (lpsOriginalJNInFractionField p hp))
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0 := by sorry
