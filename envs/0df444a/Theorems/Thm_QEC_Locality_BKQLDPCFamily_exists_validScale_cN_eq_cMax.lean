-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_validScale_cN_eq_cMax
-- name    : QEC.Locality.BKQLDPCFamily.exists_validScale_cN_eq_cMax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:03:29.698842+00:00
-- url     : https://prove2.me/theorems/81abcd70-cd8f-4889-98d4-5b3798eb1bbf
-- title:
--   BKQLDPCFamily: exists valid Scale c N eq c Max
-- statement:
--   The finite maximum is attained at an explicit scale in `[d(n), n]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L313-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L313-L319

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

theorem QEC.Locality.BKQLDPCFamily.exists_validScale_cN_eq_cMax
    (family : BKQLDPCFamily ι κ) (i : family.Index) :
    ∃ r ∈ family.validScales i, family.cN i r = family.cMax i := by sorry
