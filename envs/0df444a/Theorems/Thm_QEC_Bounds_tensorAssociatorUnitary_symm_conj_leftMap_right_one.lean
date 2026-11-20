-- Prove2me | Theorems.Thm_QEC_Bounds_tensorAssociatorUnitary_symm_conj_leftMap_right_one
-- name    : QEC.Bounds.tensorAssociatorUnitary_symm_conj_leftMap_right_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:33.168256+00:00
-- url     : https://prove2.me/theorems/1c30811b-5609-4da5-9500-57527287a187
-- title:
--   Bounds: tensor Associator Unitary symm conj left Map right one
-- statement:
--   The Bounds construction uses the tensor Associator Unitary symm conj left Map right one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L15-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L15-L30

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.tensorAssociatorUnitary_symm_conj_leftMap_right_one
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) :
    (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by sorry
