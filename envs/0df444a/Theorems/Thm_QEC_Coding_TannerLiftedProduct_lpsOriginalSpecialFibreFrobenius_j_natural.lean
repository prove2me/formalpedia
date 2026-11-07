-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreFrobenius_j_natural
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_j_natural
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:02:50.109329+00:00
-- url     : https://prove2.me/theorems/501d6ca0-156d-402b-84bc-7b335a875187
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Frobenius j natural
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Frobenius j natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L87-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L87-L92

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_j_natural :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToProjectiveJ p N hN =
      lpsOriginalSpecialFibreToProjectiveJ p N hN ≫
        absoluteFrobenius p _ (lpsOriginalProjectiveJSpecialFibreToPrimeField p) := by sorry
