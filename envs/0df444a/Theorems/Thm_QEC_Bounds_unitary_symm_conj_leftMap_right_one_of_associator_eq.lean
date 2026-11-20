-- Prove2me | Theorems.Thm_QEC_Bounds_unitary_symm_conj_leftMap_right_one_of_associator_eq
-- name    : QEC.Bounds.unitary_symm_conj_leftMap_right_one_of_associator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:52:24.306278+00:00
-- url     : https://prove2.me/theorems/48e80d19-2fe5-4963-962c-803999c97c45
-- title:
--   Bounds: unitary symm conj left Map right one of associator eq
-- statement:
--   The Bounds construction uses the unitary symm conj left Map right one of associator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L32-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L32-L47

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.unitary_symm_conj_leftMap_right_one_of_associator_eq
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (O : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)))
    (hO : O = BPTCommutingProjectorModel.tensorAssociatorUnitary H K J)
    (A : Semantics.Operator H) :
    O.symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by sorry
