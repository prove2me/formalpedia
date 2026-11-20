-- Prove2me | Theorems.Thm_QEC_Bounds_SourceFactorization_eq
-- name    : QEC.Bounds.SourceFactorization.eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:50:11.965642+00:00
-- url     : https://prove2.me/theorems/15dbfee9-97f0-4043-bb0f-4fb9b549e5bd
-- title:
--   Source Factorization: eq
-- statement:
--   The Source Factorization construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L88-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L88-L94

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.SourceFactorization.eq
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    {P A B : Semantics.Operator H} {coefficient : Complex}
    (h : SourceFactorization P A B coefficient) :
    P * A * B * P = coefficient • (P * B * P) := by sorry
