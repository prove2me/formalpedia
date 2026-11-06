-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_isometric_compression_commuting
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_isometric_compression_commuting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:26.618796+00:00
-- url     : https://prove2.me/theorems/761c0955-5afd-46bc-acac-f3fc16c41bef
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection of isometric compression commuting
-- statement:
--   Compressing an orthogonal projection to an invariant isometric subspace again
--   gives an orthogonal projection.  The second-cut use takes `J` to be the
--   chosen isotypic-sector inclusion; this is the projection input needed for
--   the source `Pi_AB'` rank-one step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Projection.lean#L29-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Projection.lean#L29-L85

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_isometric_compression_commuting
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (P : Semantics.Operator K)
    (hJadj : Jadj.comp J = (1 : Semantics.Operator H))
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hP : P.IsSymmetricProjection)
    (hcommute : Commute P (J.comp Jadj)) :
    (Jadj.comp (P.comp J)).IsSymmetricProjection := by sorry
