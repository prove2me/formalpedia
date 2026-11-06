-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_le_one
-- name    : QEC.Locality.BKQLDPCFamily.cN_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:44.291499+00:00
-- url     : https://prove2.me/theorems/a0701b2a-9e08-4dcf-ab4a-0b12f5115136
-- title:
--   BKQLDPCFamily: c N le one
-- statement:
--   The BKQLDPCFamily construction uses the c N le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L329-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L329-L339

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

theorem QEC.Locality.BKQLDPCFamily.cN_le_one (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r ≤ 1 := by sorry
