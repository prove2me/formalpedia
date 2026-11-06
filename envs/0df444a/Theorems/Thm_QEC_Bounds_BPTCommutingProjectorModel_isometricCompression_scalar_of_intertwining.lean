-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_scalar_of_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_scalar_of_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:24.90255+00:00
-- url     : https://prove2.me/theorems/63f8f94e-a992-4f63-87f4-4ea9c2aece2e
-- title:
--   BPTCommuting Projector Model: isometric Compression scalar of intertwining
-- statement:
--   Scalar compression descends through an active isometric-sector compression
--   when the probe intertwines the ambient and sector coordinates.  The probe is
--   not required to preserve the sector, which is essential for the later `C'`
--   transfer from arbitrary external-boundary probes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L122-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ActiveProjection.lean#L122-L146

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_scalar_of_intertwining
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q R : Semantics.Operator K) (Rsub : Semantics.Operator H) (scalar : Complex)
    (hleft : (J.comp Jadj).comp Q = Q)
    (hscalar : Q * R * Q = scalar • Q)
    (hintertwines : J.comp Rsub = R.comp J) :
    (Jadj.comp (Q.comp J)) * Rsub * (Jadj.comp (Q.comp J)) =
      scalar • (Jadj.comp (Q.comp J)) := by sorry
