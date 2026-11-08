-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeQuaternionKernelPoint_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimeQuaternionKernelPoint_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:45.624848+00:00
-- url     : https://prove2.me/theorems/c1bcb242-2697-4d55-83fe-2849a131737b
-- title:
--   Tanner Lifted Product: lps Prime Quaternion Kernel Point surjective
-- statement:
--   Every projective kernel line comes from a unique normalized norm-`p`
--   LPS quaternion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L387-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L387-L405

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsPrimeQuaternionKernelPoint_surjective
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    Function.Surjective (lpsPrimeQuaternionKernelPoint hp hp4) := by sorry
