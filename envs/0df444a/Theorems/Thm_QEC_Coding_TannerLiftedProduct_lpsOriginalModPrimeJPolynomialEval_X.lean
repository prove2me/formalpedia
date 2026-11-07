-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_X
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:33:19.651602+00:00
-- url     : https://prove2.me/theorems/e2929e83-3306-448d-a3a2-a90d53f06ced
-- title:
--   Tanner Lifted Product: lps Original Mod Prime JPolynomial Eval X
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Mod Prime JPolynomial Eval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L48-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L48-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_X (p : ℕ) [Fact p.Prime] :
    lpsOriginalModPrimeJPolynomialEval p Polynomial.X=
      lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero := by sorry
