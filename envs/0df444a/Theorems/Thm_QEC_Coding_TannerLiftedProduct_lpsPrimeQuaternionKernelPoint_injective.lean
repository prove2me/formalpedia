-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeQuaternionKernelPoint_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeQuaternionKernelPoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:47:21.392804+00:00
-- url     : https://prove2.me/theorems/e030d54b-ae5f-4f6f-b307-7d252c9441f9
-- title:
--   Tanner Lifted Product: lps Prime Quaternion Kernel Point injective
-- statement:
--   Distinct normalized prime quaternions have distinct kernel lines.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L308-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L308-L374

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeQuaternionKernelPoint_injective
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    Function.Injective (lpsPrimeQuaternionKernelPoint hp hp4) := by sorry
