-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_nonempty
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:01.722751+00:00
-- url     : https://prove2.me/theorems/675d2ff5-ab06-4b39-be10-95d7f4439b66
-- title:
--   Tanner Lifted Product: lps Original Special Fibre nonempty
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L47-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L47-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_nonempty
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Nonempty (lpsOriginalSpecialFibre p N hN) := by sorry
