-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_ne_zero_of_active_projection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_ne_zero_of_active_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:21.572578+00:00
-- url     : https://prove2.me/theorems/f6062dbd-4326-40bf-a006-85b2bd3b4081
-- title:
--   BPTCommuting Projector Model: isometric Compression ne zero of active projection
-- statement:
--   An active nonzero projection remains nonzero after compression to its active
--   isometric sector.  This prevents the residual `Theta` block from disappearing
--   when the common `B,C` sector is formed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L92-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L92-L114

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_ne_zero_of_active_projection
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hQ0 : Q ≠ 0)
    (hright : Q.comp (J.comp Jadj) = Q) :
    Jadj.comp (Q.comp J) ≠ 0 := by sorry
