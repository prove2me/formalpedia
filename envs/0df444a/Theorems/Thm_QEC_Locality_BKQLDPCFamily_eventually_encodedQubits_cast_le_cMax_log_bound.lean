-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_encodedQubits_cast_le_cMax_log_bound
-- name    : QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_cMax_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:13:05.019192+00:00
-- url     : https://prove2.me/theorems/86086ccf-3e44-49a6-8a20-1fae27c6d68d
-- title:
--   BKQLDPCFamily: eventually encoded Qubits cast le c Max log bound
-- statement:
--   The logarithmic two-pass bound holds on the exact valid-index tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L289-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L289-L301

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

theorem QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.EventuallyCMaxAtMostBKLogThreshold) :
    family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤
        ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
            (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by sorry
