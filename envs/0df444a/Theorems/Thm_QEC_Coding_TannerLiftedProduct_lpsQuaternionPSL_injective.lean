-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:44.125414+00:00
-- url     : https://prove2.me/theorems/6204b46c-ddc9-408e-b68d-02a748e25eff
-- title:
--   Tanner Lifted Product: lps Quaternion PSL injective
-- statement:
--   Distinct normalized shell quaternions give distinct elements of
--   `PSL(2,q)`.  Equality in the projective quotient introduces a scalar; equal
--   determinants force that scalar to be `±1`, and positivity of the normalized
--   first coordinate excludes the negative case.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L266-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L266-L338

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_injective (a : LPSResiduePrime p) :
    Function.Injective
      (fun t : {t // t ∈ lpsQuaternionShell p} =>
        lpsQuaternionPSL a t.1
          (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)) := by sorry
