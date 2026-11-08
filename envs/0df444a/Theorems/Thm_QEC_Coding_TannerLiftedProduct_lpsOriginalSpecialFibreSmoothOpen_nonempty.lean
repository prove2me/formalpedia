-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreSmoothOpen_nonempty
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpen_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:34:23.457197+00:00
-- url     : https://prove2.me/theorems/7d9186ec-4fb5-451e-a44a-a2e846a646b1
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Smooth Open nonempty
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Smooth Open nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L68-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpen_nonempty
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Nonempty (lpsOriginalSpecialFibreSmoothLocus p N hN).toScheme := by sorry
