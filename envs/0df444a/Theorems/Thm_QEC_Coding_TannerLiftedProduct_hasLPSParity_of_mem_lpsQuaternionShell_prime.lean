-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_of_mem_lpsQuaternionShell_prime
-- name    : QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:46:01.24699+00:00
-- url     : https://prove2.me/theorems/5433afce-127e-4431-ae7b-ecdc2ea06e82
-- title:
--   Tanner Lifted Product: has LPSParity of mem lps Quaternion Shell prime
-- statement:
--   The usual LPS parity statement for a normalized prime shell, without
--   packaging an auxiliary residue prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L188-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L188-L204

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell_prime
    (hp4 : p % 4 = 1) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.HasLPSParity := by sorry
