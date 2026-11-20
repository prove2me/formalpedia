-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:30:11.540059+00:00
-- url     : https://prove2.me/theorems/3f779511-65da-4099-8261-d30c7e0f0c0b
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue Fraction Map integer Coefficient
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue Fraction Map integer Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L29-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L29-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by sorry
