-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_le_scale
-- name    : QEC.Locality.twoThirdsSeparationProfile_le_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:10:36.661196+00:00
-- url     : https://prove2.me/theorems/8ada4250-8d18-4bb3-84f5-6f81f9ae9768
-- title:
--   Locality: two Thirds Separation Profile le scale
-- statement:
--   The measured profile at scale `r` never exceeds `r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L112-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L112-L122

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v

theorem QEC.Locality.twoThirdsSeparationProfile_le_scale
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) :
    twoThirdsSeparationProfile G scale ≤ scale := by sorry
