-- Prove2me | Theorems.Thm_QEC_Bounds_intertwining_precompose_associator_right_of_eq
-- name    : QEC.Bounds.intertwining_precompose_associator_right_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:50:59.849609+00:00
-- url     : https://prove2.me/theorems/6f4c462b-75ad-41a6-a1a4-2b9bd6dcd2e0
-- title:
--   Bounds: intertwining precompose associator right of eq
-- statement:
--   The Bounds construction uses the intertwining precompose associator right of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L202-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L202-L244

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000

theorem QEC.Bounds.intertwining_precompose_associator_right_of_eq
    {H K J T : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    (O : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)))
    (hO : O = BPTCommutingProjectorModel.tensorAssociatorUnitary H K J)
    (E : Semantics.CompositeSystem H (Semantics.CompositeSystem K J) →ₗ[Complex] T)
    (Enew : Semantics.CompositeSystem (Semantics.CompositeSystem H K) J →ₗ[Complex] T)
    (hEnew : Enew = E.comp O.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator T) (R : Semantics.Operator J)
    (hE : P.comp E = E.comp
      (TensorProduct.map (1 : Semantics.Operator H)
        (TensorProduct.map (1 : Semantics.Operator K) R))) :
    P.comp Enew = Enew.comp
      (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R) := by sorry
