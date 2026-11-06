-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_lt_scale
-- name    : QEC.Locality.twoThirdsSeparationProfile_lt_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:06.966196+00:00
-- url     : https://prove2.me/theorems/815b9ae7-5743-4d10-8cde-b8ff6d184d14
-- title:
--   Locality: two Thirds Separation Profile lt scale
-- statement:
--   At every scale at least two, the measured profile is strictly below its scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L144-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L144-L161

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v

theorem QEC.Locality.twoThirdsSeparationProfile_lt_scale
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {scale : Nat} (hscale : 2 ≤ scale) :
    twoThirdsSeparationProfile G scale < scale := by sorry
