-- Prove2me | Theorems.Thm_QEC_Bounds_reassociated_rankOne_isometric_lift
-- name    : QEC.Bounds.reassociated_rankOne_isometric_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:45.3886+00:00
-- url     : https://prove2.me/theorems/a66573cd-a0e5-4369-bb21-8b7aaab32d60
-- title:
--   Bounds: reassociated rank One isometric lift
-- statement:
--   The Bounds construction uses the reassociated rank One isometric lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L125-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L125-L166

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.reassociated_rankOne_isometric_lift
    {H K J X : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (E : Semantics.CompositeSystem H (Semantics.CompositeSystem K J) →ₗ[Complex] X)
    (phi : H) (chi : K) (Q : Semantics.Operator J) :
    let O := BPTCommutingProjectorModel.tensorAssociatorUnitary H K J
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    Enew.comp
        ((TensorProduct.map
          (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
            (phi ⊗ₜ[Complex] chi)).toLinearMap Q).comp
          (LinearMap.adjoint Enew)) =
      E.comp
        ((TensorProduct.map
          (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (TensorProduct.map
            (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)).comp
          (LinearMap.adjoint E)) := by sorry
