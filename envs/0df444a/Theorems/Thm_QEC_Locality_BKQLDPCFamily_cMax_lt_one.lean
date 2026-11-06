-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cMax_lt_one
-- name    : QEC.Locality.BKQLDPCFamily.cMax_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:59:41.560668+00:00
-- url     : https://prove2.me/theorems/04cc7160-cd76-4824-9152-5fd0d6f97054
-- title:
--   BKQLDPCFamily: c Max lt one
-- statement:
--   The BKQLDPCFamily construction uses the c Max lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L366-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L366-L370

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

theorem QEC.Locality.BKQLDPCFamily.cMax_lt_one (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i < 1 := by sorry
