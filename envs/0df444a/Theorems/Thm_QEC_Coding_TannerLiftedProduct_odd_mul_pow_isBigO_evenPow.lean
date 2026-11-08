-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_odd_mul_pow_isBigO_evenPow
-- name    : QEC.Coding.TannerLiftedProduct.odd_mul_pow_isBigO_evenPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:12.668918+00:00
-- url     : https://prove2.me/theorems/a1be5880-da7b-4176-9add-c8f5864995e5
-- title:
--   Tanner Lifted Product: odd mul pow is Big O even Pow
-- statement:
--   A linear factor times `pⁿ` is exponentially bounded at every even-power
--   rate whose base is strictly larger than `√p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L156-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L156-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.odd_mul_pow_isBigO_evenPow
    {p t : ℝ} (hp : 0 ≤ p) (ht : Real.sqrt p < t) :
    (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * p ^ n) =O[atTop]
      fun n : ℕ => t ^ (2 * n) := by sorry
