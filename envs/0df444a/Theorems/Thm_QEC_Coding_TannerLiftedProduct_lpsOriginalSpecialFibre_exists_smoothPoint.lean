-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_exists_smoothPoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_exists_smoothPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:34:21.828521+00:00
-- url     : https://prove2.me/theorems/1685489e-c81e-4034-ab0c-4efefb8596cb
-- title:
--   Tanner Lifted Product: lps Original Special Fibre exists smooth Point
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre exists smooth Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L44-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSmoothSpecialFiber.lean#L44-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_exists_smoothPoint
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    ∃ x : lpsOriginalSpecialFibre p N hN,
      x ∈ lpsOriginalSpecialFibreSmoothLocus p N hN := by sorry
