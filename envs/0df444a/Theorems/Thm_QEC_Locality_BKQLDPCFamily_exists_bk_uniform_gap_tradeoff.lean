-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_bk_uniform_gap_tradeoff
-- name    : QEC.Locality.BKQLDPCFamily.exists_bk_uniform_gap_tradeoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:34.964075+00:00
-- url     : https://prove2.me/theorems/2f051afc-61e8-4b47-9857-592495a973c4
-- title:
--   BKQLDPCFamily: exists bk uniform gap tradeoff
-- statement:
--   The uniform-gap BK terminal, retaining the pointwise measured `cMax` in the
--   distance exponent while using a family-uniform coefficient ceiling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/ConnectivitySeparator.lean#L106-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/ConnectivitySeparator.lean#L106-L127

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

theorem QEC.Locality.BKQLDPCFamily.exists_bk_uniform_gap_tradeoff
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices)
    (huniform : family.UniformCMaxBelowOne) :
    ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
        (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1))) := by sorry
