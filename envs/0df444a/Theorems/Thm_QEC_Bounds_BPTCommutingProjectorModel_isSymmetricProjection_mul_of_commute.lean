-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_mul_of_commute
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_mul_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:43.387969+00:00
-- url     : https://prove2.me/theorems/0dc7875f-e2a6-4814-ac28-791ddaf5cfeb
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection mul of commute
-- statement:
--   The product of two commuting finite-dimensional orthogonal projectors is again
--   an orthogonal projector.  This closes the elementary projector algebra needed
--   to apply the joint spectral theorem to BPT's two source cuts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2519-L2538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2519-L2538

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_mul_of_commute {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] {P Q : Semantics.Operator H}
    (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hcommute : Commute P Q) : (P * Q).IsSymmetricProjection := by sorry
