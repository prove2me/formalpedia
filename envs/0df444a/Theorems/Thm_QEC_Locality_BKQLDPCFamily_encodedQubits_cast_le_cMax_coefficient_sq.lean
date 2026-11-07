-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_encodedQubits_cast_le_cMax_coefficient_sq
-- name    : QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_cMax_coefficient_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:14.929096+00:00
-- url     : https://prove2.me/theorems/013a4b47-daa9-4851-994a-9a6e6e10e1fd
-- title:
--   BKQLDPCFamily: encoded Qubits cast le c Max coefficient sq
-- statement:
--   The measured `cMax` profile gives the exact finite two-pass BK dimension estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L156-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L156-L179

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

theorem QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_cMax_coefficient_sq
    (family : BKQLDPCFamily iota kappa) (i : family.Index) :
    (family.encodedQubits i.1 : ℝ) ≤
      (bkRpowCoefficient 1 (family.cMax i) *
          bkRpowCoefficient 1 (family.cMax i)) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by sorry
