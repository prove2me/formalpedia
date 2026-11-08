-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_flat
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_flat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:05:19.668686+00:00
-- url     : https://prove2.me/theorems/a7efb30f-7936-408d-b6a9-3110f8013bee
-- title:
--   Tanner Lifted Product: lps Original Special Fibre To Prime Field flat
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre To Prime Field flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L23-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L23-L29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_flat
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Flat (lpsOriginalSpecialFibreToPrimeField p N hN) := by sorry
