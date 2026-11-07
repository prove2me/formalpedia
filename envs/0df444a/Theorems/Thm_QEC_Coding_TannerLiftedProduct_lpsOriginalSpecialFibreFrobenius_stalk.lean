-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreFrobenius_stalk
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_stalk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:00:12.518062+00:00
-- url     : https://prove2.me/theorems/8212492d-b72c-4ed5-9f20-36bb4fa6993d
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Frobenius stalk
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Frobenius stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L39-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFibreFrobenius.lean#L39-L42

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_stalk (x : lpsOriginalSpecialFibre p N hN)
    (s : (lpsOriginalSpecialFibre p N hN).presheaf.stalk x) :
    (lpsOriginalSpecialFibreFrobenius p N hN).stalkMap x s = s^p := by sorry
