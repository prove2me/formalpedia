-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternion_eq_of_matrix_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternion_eq_of_matrix_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:58.113264+00:00
-- url     : https://prove2.me/theorems/75c86ece-70da-40ea-8f42-4aeaf2ad290e
-- title:
--   Tanner Lifted Product: lps Quaternion eq of matrix eq
-- statement:
--   Reduction modulo the residue prime is injective on the normalized shell
--   already at the matrix level.  The stored bound `q > 4p` is stronger than the
--   `q > 2p` needed to recover each integral coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L150-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L150-L225

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternion_eq_of_matrix_eq
    (a : LPSResiduePrime p) {t u : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p)
    (hu : u ∈ lpsQuaternionShell p)
    (hM : lpsQuaternionMatrix a.q t = lpsQuaternionMatrix a.q u) :
    t = u := by sorry
