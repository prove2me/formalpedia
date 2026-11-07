-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_encodedQubits_cast_le_cMax_log_bound
-- name    : QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_cMax_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:01.252721+00:00
-- url     : https://prove2.me/theorems/d13d11c4-dc81-4dc0-a8b9-7c20ff44f060
-- title:
--   BKQLDPCFamily: encoded Qubits cast le c Max log bound
-- statement:
--   The pointwise BK logarithmic threshold gives the explicit two-pass logarithmic bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L182-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L182-L233

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

theorem QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    (hthreshold : family.cMax i ≤
      1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ)) :
    (family.encodedQubits i.1 : ℝ) ≤
      ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
          (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by sorry
