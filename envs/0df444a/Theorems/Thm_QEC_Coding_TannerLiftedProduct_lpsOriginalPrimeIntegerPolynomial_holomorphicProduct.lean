-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_holomorphicProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_holomorphicProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:29:48.250605+00:00
-- url     : https://prove2.me/theorems/53b41d12-41d1-4cb6-8506-a99ea7be9940
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial holomorphic Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial holomorphic Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L258-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L258-L268

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_holomorphicProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map lpsOriginalJHolomorphicEvalZ=
      ∏ i : Option (Fin p),
        (Polynomial.X-Polynomial.C (lpsOriginalPrimeBranchHolomorphic p i)) := by sorry
