-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:58:21.522588+00:00
-- url     : https://prove2.me/theorems/1d7b732d-8403-4ab4-b07d-3dc913c3e8fa
-- title:
--   Tanner Lifted Product: lps Original Special Fibre To Prime Field locally Of Finite Presentation
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre To Prime Field locally Of Finite Presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L39-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L39-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalSpecialFibreToPrimeField p N hN) := by sorry
