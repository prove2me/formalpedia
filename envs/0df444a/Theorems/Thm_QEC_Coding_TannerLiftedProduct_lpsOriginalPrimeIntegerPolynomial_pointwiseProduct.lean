-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:00.765104+00:00
-- url     : https://prove2.me/theorems/44a11fab-50dd-4580-914c-30a94de21559
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial pointwise Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial pointwise Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L270-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L270-L300

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
    (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeBranch p i τ)) := by sorry
