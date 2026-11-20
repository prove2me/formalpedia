-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sourceFactorization_of_rankOneLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_rankOneLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:20:37.647837+00:00
-- url     : https://prove2.me/theorems/7131ee9c-2d65-4e54-ae2c-74d0ffcf9446
-- title:
--   BPTCommuting Projector Model: source Factorization of rank One Lift
-- statement:
--   The BPT source equation survives a common ambient isometric lift.  The first
--   probe is supplied as a compression, while the exterior probe has the stronger
--   range-intertwining identity that prevents an unproved insertion of the range
--   projection between the two source operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L322-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L322-L403

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.sourceFactorization_of_rankOneLift
    {H K X : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (embedding : Semantics.CompositeSystem H K →ₗ[Complex] X)
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (leftAmbient rightAmbient : Semantics.Operator X)
    (leftLocal : Semantics.Operator H) (rightLocal : Semantics.Operator K)
    (hisometry : (LinearMap.adjoint embedding).comp embedding =
      (1 : Semantics.Operator (Semantics.CompositeSystem H K)))
    (hleft : (LinearMap.adjoint embedding).comp (leftAmbient.comp embedding) =
      TensorProduct.map leftLocal (1 : Semantics.Operator K))
    (hright : rightAmbient.comp embedding = embedding.comp
      (TensorProduct.map (1 : Semantics.Operator H) rightLocal)) :
    let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    let productProjector := TensorProduct.map rankOne Q
    let liftedProjector := embedding.comp (productProjector.comp (LinearMap.adjoint embedding))
    liftedProjector * leftAmbient * rightAmbient * liftedProjector =
      (inner Complex phi (leftLocal phi)) •
        (liftedProjector * rightAmbient * liftedProjector) := by sorry
