-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_index_card
-- name    : QEC.Locality.BKQLDPCFamily.index_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:52.083268+00:00
-- url     : https://prove2.me/theorems/92a5ca15-4573-4067-83e3-922b4aa5bfda
-- title:
--   BKQLDPCFamily: index card
-- statement:
--   The selected family index is exactly the physical block length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L222-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L222-L224

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

theorem QEC.Locality.BKQLDPCFamily.index_card (family : BKQLDPCFamily ι κ) (i : family.Index) :
    Fintype.card (ι i.1) = i.1 := by sorry
