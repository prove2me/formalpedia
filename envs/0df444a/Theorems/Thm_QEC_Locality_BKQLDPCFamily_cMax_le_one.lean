-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cMax_le_one
-- name    : QEC.Locality.BKQLDPCFamily.cMax_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:09:04.182496+00:00
-- url     : https://prove2.me/theorems/b39390e0-e268-4909-9dc9-7f99cb1a2da7
-- title:
--   BKQLDPCFamily: c Max le one
-- statement:
--   The BKQLDPCFamily construction uses the c Max le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L360-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L360-L364

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

theorem QEC.Locality.BKQLDPCFamily.cMax_le_one (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i ≤ 1 := by sorry
