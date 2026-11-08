-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseVoltage_decode
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseVoltage_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:11:18.562195+00:00
-- url     : https://prove2.me/theorems/da2edc67-63ab-44d6-963c-f82cc22b1de2
-- title:
--   Tanner Lifted Product: lps Sparse Voltage decode
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse Voltage decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L40-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseVoltage_decode {q D : ℕ} [Fact q.Prime]
    (label : Fin D → LPSSparseGroupIndex q) (side : Fin 2) (j : Fin D) :
    (lpsPSLEnumerationEquiv q) (lpsSparseVoltage label side j) =
      doubleCoverVoltage (fun j => (lpsPSLEnumerationEquiv q) (label j)) side j := by sorry
