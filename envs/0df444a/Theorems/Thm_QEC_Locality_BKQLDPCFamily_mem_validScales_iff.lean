-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_mem_validScales_iff
-- name    : QEC.Locality.BKQLDPCFamily.mem_validScales_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:59:35.566569+00:00
-- url     : https://prove2.me/theorems/dc093a55-3091-4724-a1ff-5269cdc96972
-- title:
--   BKQLDPCFamily: mem valid Scales iff
-- statement:
--   Membership unfolds to the exact natural range `d(n) <= r <= n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L233-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L233-L236

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

theorem QEC.Locality.BKQLDPCFamily.mem_validScales_iff (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) :
    r ∈ family.validScales i ↔ family.distance i.1 ≤ r ∧ r ≤ i.1 := by sorry
