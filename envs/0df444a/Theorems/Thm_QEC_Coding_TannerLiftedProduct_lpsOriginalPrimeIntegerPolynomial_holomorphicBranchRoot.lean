-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:07.443528+00:00
-- url     : https://prove2.me/theorems/e749773e-c682-4536-8542-cb5276d8ce5f
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial holomorphic Branch Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial holomorphic Branch Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L186-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L186-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      lpsOriginalJHolomorphicEvalZ (lpsOriginalPrimeBranchHolomorphic p i)=0 := by sorry
