-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_encodedQubits_cast_le_cMax_logarithmic_gap_bound
-- name    : QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_cMax_logarithmic_gap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:35.16223+00:00
-- url     : https://prove2.me/theorems/f16a5324-29f3-4765-8d75-c3653932cf0e
-- title:
--   BKQLDPCFamily: eventually encoded Qubits cast le c Max logarithmic gap bound
-- statement:
--   The two-pass logarithmic-gap bound holds on the explicit valid-index tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L304-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L304-L317

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

theorem QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) {gamma : ℝ} (hgamma : 0 < gamma)
    (hfamily : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤
        ((3 * Real.log i.1 / (bkEntropyGap * gamma)) *
            (3 * Real.log i.1 / (bkEntropyGap * gamma))) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by sorry
