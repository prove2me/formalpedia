-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_residue_expansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_residue_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:42:18.594648+00:00
-- url     : https://prove2.me/theorems/801c919b-3b92-436a-b4b7-c7c6b0439278
-- title:
--   Tanner Lifted Product: lps Theta residue expansion
-- statement:
--   Exact residue-class expansion of the actual Jacobi theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L102-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean#L102-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_residue_expansion (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (z+2*(a:ℂ)/(c:ℂ)) =
      ∑ r : Fin c, lpsQuadraticPhase a c r *
        lpsShiftedTheta ((r.val:ℂ)/(c:ℂ)) ((c:ℂ)^2*z) := by sorry
