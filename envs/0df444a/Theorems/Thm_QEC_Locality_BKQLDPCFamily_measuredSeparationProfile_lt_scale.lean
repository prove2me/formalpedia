-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_lt_scale
-- name    : QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_lt_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:59.189203+00:00
-- url     : https://prove2.me/theorems/64d0ea6b-f8ec-4d73-9e62-332b96fcee4c
-- title:
--   BKQLDPCFamily: measured Separation Profile lt scale
-- statement:
--   The observed profile is strictly below every source-valid scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L265-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L265-L272

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

theorem QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_lt_scale (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.measuredSeparationProfile i r < r := by sorry
