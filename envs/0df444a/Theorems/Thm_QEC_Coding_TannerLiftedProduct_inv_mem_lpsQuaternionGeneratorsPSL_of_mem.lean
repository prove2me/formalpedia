-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_inv_mem_lpsQuaternionGeneratorsPSL_of_mem
-- name    : QEC.Coding.TannerLiftedProduct.inv_mem_lpsQuaternionGeneratorsPSL_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:50.490197+00:00
-- url     : https://prove2.me/theorems/21859568-7e9e-4366-b972-f177e77bc7ed
-- title:
--   Tanner Lifted Product: inv mem lps Quaternion Generators PSL of mem
-- statement:
--   The Tanner Lifted Product construction uses the inv mem lps Quaternion Generators PSL of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L349-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L349-L361

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.inv_mem_lpsQuaternionGeneratorsPSL_of_mem
    (a : LPSResiduePrime p) {g : PSL(2, ZMod a.q)}
    (hg : g ∈ lpsQuaternionGeneratorsPSL a) :
    g⁻¹ ∈ lpsQuaternionGeneratorsPSL a := by sorry
