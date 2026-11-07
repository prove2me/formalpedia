-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_sum_residue_blocks
-- name    : QEC.Coding.TannerLiftedProduct.lpsZMod_sum_residue_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:19.209771+00:00
-- url     : https://prove2.me/theorems/f0a42228-37fc-4c99-b56d-64070c22888d
-- title:
--   Tanner Lifted Product: lps ZMod sum residue blocks
-- statement:
--   Interchanging block sizes exposes the residue modulo the scaling factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L113-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L113-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsZMod_sum_residue_blocks (d m : ℕ) [NeZero d] [NeZero m]
    (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin m, ∑ j : Fin d, f ((j.val+d*i.val:ℕ):ZMod (d*m)) := by sorry
