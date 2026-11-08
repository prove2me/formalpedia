-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
-- name    : QEC.Coding.TannerLiftedProduct.eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:46:50.460309+00:00
-- url     : https://prove2.me/theorems/bd5a42e5-aed8-42dd-bdaf-d25216b15a4a
-- title:
--   Tanner Lifted Product: eq one or neg one of norm eq one of has LPSParity
-- statement:
--   The only norm-one integral quaternions in the LPS parity class are the
--   two central units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L263-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L263-L293

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
    (t : LPSQuaternion) (hnorm : t.norm = 1)
    (hparity : t.HasLPSParity) : t = 1 ∨ t = -1 := by sorry
