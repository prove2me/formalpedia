-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_le_scale
-- name    : QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:16.090297+00:00
-- url     : https://prove2.me/theorems/700bf33a-f4ef-4904-abea-3e8a3bed8dac
-- title:
--   BKQLDPCFamily: measured Separation Profile le scale
-- statement:
--   The observed profile is bounded by its natural scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L259-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L259-L262

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

theorem QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_scale (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) :
    family.measuredSeparationProfile i r ≤ r := by sorry
