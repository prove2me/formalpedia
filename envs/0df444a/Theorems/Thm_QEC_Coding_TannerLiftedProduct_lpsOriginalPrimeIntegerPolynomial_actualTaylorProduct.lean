-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:21.320097+00:00
-- url     : https://prove2.me/theorems/46424242-9944-45c0-9d20-7d933dd18686
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial actual Taylor Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial actual Taylor Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L74-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L74-L105

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct (p : ℕ) [Fact p.Prime] :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalAnalyticPrimeCoefficientEval p)).map lpsOriginalAnalyticCuspLocalizedTaylor=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by sorry
