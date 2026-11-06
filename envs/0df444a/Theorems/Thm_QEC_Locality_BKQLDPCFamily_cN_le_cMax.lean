-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_le_cMax
-- name    : QEC.Locality.BKQLDPCFamily.cN_le_cMax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:41.766617+00:00
-- url     : https://prove2.me/theorems/af942f54-794e-4181-bedd-79e13b090a61
-- title:
--   BKQLDPCFamily: c N le c Max
-- statement:
--   Every observed scale exponent is bounded by the attained finite maximum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L373-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L373-L377

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

theorem QEC.Locality.BKQLDPCFamily.cN_le_cMax (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r ≤ family.cMax i := by sorry
