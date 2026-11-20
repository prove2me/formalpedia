-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:30:32.843155+00:00
-- url     : https://prove2.me/theorems/9a230b8e-1fad-4d3c-bfb4-e6662529c7b7
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial gauss Maximal Residue Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial gauss Maximal Residue Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L43-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L43-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q))
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by sorry
