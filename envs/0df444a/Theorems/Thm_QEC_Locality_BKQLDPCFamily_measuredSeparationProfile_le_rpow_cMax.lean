-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_measuredSeparationProfile_le_rpow_cMax
-- name    : QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_rpow_cMax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:40.96089+00:00
-- url     : https://prove2.me/theorems/679d6d86-3711-456e-9bed-875e8184fa3e
-- title:
--   BKQLDPCFamily: measured Separation Profile le rpow c Max
-- statement:
--   The measured profile upper bound is derived from the observed finite maximum.
--   It is not an assumption field and is stated only on the source interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L397-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L397-L405

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

theorem QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_rpow_cMax
    (family : BKQLDPCFamily ι κ) (i : family.Index)
    {r : Nat} (hr : r ∈ family.validScales i) :
    (family.measuredSeparationProfile i r : ℝ) ≤
      Real.rpow (r : ℝ) (family.cMax i) := by sorry
