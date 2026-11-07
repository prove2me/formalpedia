-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:06.697253+00:00
-- url     : https://prove2.me/theorems/8f139982-f72a-4289-9ec1-dbb17723ad4d
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial degree
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L49-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L49-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_degree (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).natDegree=p+1 := by sorry
