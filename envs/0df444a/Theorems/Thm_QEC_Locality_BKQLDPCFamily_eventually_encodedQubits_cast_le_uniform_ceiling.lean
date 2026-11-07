-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_encodedQubits_cast_le_uniform_ceiling
-- name    : QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_uniform_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:04:33.412053+00:00
-- url     : https://prove2.me/theorems/27ca7504-aa4f-469e-90ae-57a8e06fe092
-- title:
--   BKQLDPCFamily: eventually encoded Qubits cast le uniform ceiling
-- statement:
--   `UniformCMaxBelowOne` supplies one log-free two-pass tail and its constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L390-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean#L390-L404

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

theorem QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (family.encodedQubits i.1 : ℝ) ≤
          ((3 / (bkEntropyGap * (1 - ceiling))) *
              (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
            (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
              ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by sorry
