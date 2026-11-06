-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_left_support_of_right_support
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_left_support_of_right_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:50:13.282602+00:00
-- url     : https://prove2.me/theorems/f50f1916-7ab0-4325-9703-6eeb049e6ba3
-- title:
--   BPTCommuting Projector Model: isometric Compression left support of right support
-- statement:
--   An orthogonal projection supported on an isometric sector is supported from
--   both sides.  This is the algebraic form needed before compressing the actual
--   second-cut right block to the active first-cut `C` sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L42-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L42-L64

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_left_support_of_right_support
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (J.comp Jadj).comp Q = Q := by sorry
