-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:04:57.658471+00:00
-- url     : https://prove2.me/theorems/d559a413-76f0-4322-81d4-79bb870993f2
-- title:
--   Tanner Lifted Product: lps Original Special Fibre To Prime Field surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre To Prime Field surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L31-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFlat.lean#L31-L37

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_surjective
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalSpecialFibreToPrimeField p N hN) := by sorry
