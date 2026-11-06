-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_conjDensity_pureDensity
-- name    : QEC.Bounds.BPTEntropy.conjDensity_pureDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:16.332254+00:00
-- url     : https://prove2.me/theorems/db67e5ef-2d2d-4f3b-a5d0-657b108a3535
-- title:
--   BPTEntropy: conj Density pure Density
-- statement:
--   A unitary transport sends a normalized rank-one density to the rank-one
--   density of its transported vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L111-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L111-L122

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.conjDensity_pureDensity {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    U.conjDensity (pureDensity psi hpsi) =
      pureDensity (U psi) (by
        change ‖U.toLinearIsometryEquiv psi‖ ^ 2 = 1
        rw [U.toLinearIsometryEquiv.norm_map]
        exact hpsi) := by sorry
