-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_active_isometric_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_active_isometric_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:18.346902+00:00
-- url     : https://prove2.me/theorems/e0a666f0-cec2-40f2-93f2-f3f694a18d8f
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection of active isometric compression
-- statement:
--   Compressing an active orthogonal projection to an isometric sector preserves
--   orthogonal-projection structure.  Unlike a bare compression statement, the
--   active-sector hypothesis supplies the required invariance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L71-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L71-L85

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_active_isometric_compression
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj : Jadj.comp J = (1 : Semantics.Operator H))
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (Jadj.comp (Q.comp J)).IsSymmetricProjection := by sorry
