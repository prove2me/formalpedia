-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_nonneg
-- name    : QEC.Locality.BKQLDPCFamily.cN_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:30.853812+00:00
-- url     : https://prove2.me/theorems/cdaae40a-831e-4763-90f0-6be9cb4cf578
-- title:
--   BKQLDPCFamily: c N nonneg
-- statement:
--   Every observed exponent lies in the source-valid closed range `[0, 1]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L322-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L322-L327

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

theorem QEC.Locality.BKQLDPCFamily.cN_nonneg (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    0 ≤ family.cN i r := by sorry
