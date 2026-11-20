-- Prove2me | Theorems.Thm_QEC_Bounds_isometric_lift_congr
-- name    : QEC.Bounds.isometric_lift_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:49:56.042634+00:00
-- url     : https://prove2.me/theorems/4308ab7c-2575-449d-ab2b-22c2b3246e01
-- title:
--   Bounds: isometric lift congr
-- statement:
--   The Bounds construction uses the isometric lift congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L72-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/CompressionAlgebra.lean#L72-L80

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u

theorem QEC.Bounds.isometric_lift_congr
    {S K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator S} (h : P = Q) :
    E.comp (P.comp (LinearMap.adjoint E)) =
      E.comp (Q.comp (LinearMap.adjoint E)) := by sorry
