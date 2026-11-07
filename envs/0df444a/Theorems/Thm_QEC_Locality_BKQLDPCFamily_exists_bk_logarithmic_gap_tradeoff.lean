-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_bk_logarithmic_gap_tradeoff
-- name    : QEC.Locality.BKQLDPCFamily.exists_bk_logarithmic_gap_tradeoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:36.765274+00:00
-- url     : https://prove2.me/theorems/b8949633-2d31-42a2-bca3-4bc418271e72
-- title:
--   BKQLDPCFamily: exists bk logarithmic gap tradeoff
-- statement:
--   The source-narrowed, Lean-QEC-repaired logarithmic BK terminal.
--
--   The `gamma` premise is visible and family-uniform.  It controls the measured
--   exponent only on a valid-index tail; it supplies neither a partition nor a
--   recovery, both of which come from the actual two-pass construction in #381.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/ConnectivitySeparator.lean#L77-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/ConnectivitySeparator.lean#L77-L100

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Definitions.Def_QEC_Results_LocalityBounds_ConnectivitySeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

theorem QEC.Locality.BKQLDPCFamily.exists_bk_logarithmic_gap_tradeoff
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
        (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)) *
          (Real.log i.1) ^ 2) := by sorry
