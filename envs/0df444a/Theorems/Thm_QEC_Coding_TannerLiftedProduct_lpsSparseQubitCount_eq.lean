-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseQubitCount_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseQubitCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:56:05.686232+00:00
-- url     : https://prove2.me/theorems/6e1d6130-b80b-4e5e-965a-cc7e5beec708
-- title:
--   Tanner Lifted Product: lps Sparse Qubit Count eq
-- statement:
--   The numeric physical extent is the source face-plus-vertex count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L413-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L413-L415

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseQubitCount_eq {q D r r' : ℕ} [Fact q.Prime] :
    D * (D * (lpsPSLList q).length) + (2 * r) * ((2 * r') * (lpsPSLList q).length) =
      (lpsPSLList q).length * (D ^ 2 + 4 * r * r') := by sorry
