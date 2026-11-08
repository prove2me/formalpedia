-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreFrobenius_overPrimeField
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_overPrimeField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:00:31.489262+00:00
-- url     : https://prove2.me/theorems/ca0080ae-8a99-4017-a0ac-fd891ed66203
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Frobenius over Prime Field
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Frobenius over Prime Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L53-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L53-L56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_overPrimeField :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToPrimeField p N hN =
      lpsOriginalSpecialFibreToPrimeField p N hN := by sorry
