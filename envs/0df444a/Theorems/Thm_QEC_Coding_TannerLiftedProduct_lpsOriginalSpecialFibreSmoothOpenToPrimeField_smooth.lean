-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreSmoothOpenToPrimeField_smooth
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpenToPrimeField_smooth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:35:04.570763+00:00
-- url     : https://prove2.me/theorems/96a468a6-e8bb-49c4-825e-93577274095c
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Smooth Open To Prime Field smooth
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Smooth Open To Prime Field smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L58-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L58-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpenToPrimeField_smooth
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    Smooth (lpsOriginalSpecialFibreSmoothOpenToPrimeField p N hN) := by sorry
