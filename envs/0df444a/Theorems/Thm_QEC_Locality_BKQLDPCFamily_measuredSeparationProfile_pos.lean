-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_pos
-- name    : QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:59:31.591266+00:00
-- url     : https://prove2.me/theorems/7c1b4490-054e-41b8-b534-a4f1d1f28b8a
-- title:
--   BKQLDPCFamily: measured Separation Profile pos
-- statement:
--   The measured graph profile is positive throughout the source scale interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L248-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L248-L256

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

theorem QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_pos (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    0 < family.measuredSeparationProfile i r := by sorry
