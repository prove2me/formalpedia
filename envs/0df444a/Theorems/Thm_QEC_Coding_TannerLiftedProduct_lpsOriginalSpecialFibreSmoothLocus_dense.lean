-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreSmoothLocus_dense
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothLocus_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:34:22.596548+00:00
-- url     : https://prove2.me/theorems/8606766a-0c62-4ea9-98b1-6171f72c6ac4
-- title:
--   Tanner Lifted Product: lps Original Special Fibre Smooth Locus dense
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre Smooth Locus dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L34-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L34-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothLocus_dense
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Dense (lpsOriginalSpecialFibreSmoothLocus p N hN :
      Set (lpsOriginalSpecialFibre p N hN)) := by sorry
