-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_encodedQubits_cast_le_uniform_ceiling
-- name    : QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_uniform_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:14.145171+00:00
-- url     : https://prove2.me/theorems/636e19b1-3c92-4727-b812-b0183198ea96
-- title:
--   BKQLDPCFamily: encoded Qubits cast le uniform ceiling
-- statement:
--   A family-uniform exponent ceiling below one removes the logarithmic coefficient.
--   The distance exponent remains the sharper pointwise `cMax` exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L323-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L323-L387

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

theorem QEC.Locality.BKQLDPCFamily.encodedQubits_cast_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {ceiling : ℝ} (_hceiling0 : 0 ≤ ceiling) (hceiling1 : ceiling < 1)
    (hcMax : family.cMax i ≤ ceiling) :
    (family.encodedQubits i.1 : ℝ) ≤
      ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
        (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
          ((family.distance i.1 : ℝ) ^ (1 - family.cMax i))) := by sorry
