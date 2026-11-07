-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_sum_blocks
-- name    : QEC.Coding.TannerLiftedProduct.lpsZMod_sum_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:01.63921+00:00
-- url     : https://prove2.me/theorems/54248bc6-d243-49ca-abc7-ae570e2b0b2c
-- title:
--   Tanner Lifted Product: lps ZMod sum blocks
-- statement:
--   Actual residue blocks reindex the complete cyclic sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L67-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L67-L77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsZMod_sum_blocks (d m : ℕ) [NeZero d] [NeZero m] (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin d, ∑ j : Fin m, f ((j.val+m*i.val:ℕ):ZMod (d*m)) := by sorry
