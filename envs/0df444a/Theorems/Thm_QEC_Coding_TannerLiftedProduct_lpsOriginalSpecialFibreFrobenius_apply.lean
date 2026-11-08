-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreFrobenius_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:00:00.568832+00:00
-- url     : https://prove2.me/theorems/e0989ba2-e7fc-4def-82a3-e28e33b25a4b
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Frobenius apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Frobenius apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L44-L46

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_apply (x : lpsOriginalSpecialFibre p N hN) :
    lpsOriginalSpecialFibreFrobenius p N hN x = x := by sorry
