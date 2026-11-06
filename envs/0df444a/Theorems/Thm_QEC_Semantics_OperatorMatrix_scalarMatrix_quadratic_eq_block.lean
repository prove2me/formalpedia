-- Prove2me | Theorems.Thm_QEC_Semantics_OperatorMatrix_scalarMatrix_quadratic_eq_block
-- name    : QEC.Semantics.OperatorMatrix.scalarMatrix_quadratic_eq_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:37.420224+00:00
-- url     : https://prove2.me/theorems/ac7ff45b-00ef-4a8a-bd83-08702983357b
-- title:
--   Operator Matrix: scalar Matrix quadratic eq block
-- statement:
--   The scalar quadratic form is the block quadratic form evaluated on the vector
--   whose basis coefficients are the conjugates of the scalar test vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L150-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L150-L172

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.OperatorMatrix.scalarMatrix_quadratic_eq_block {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (b : OrthonormalBasis β Complex H)
    (c : Fin n × β → Complex) :
    dotProduct (star c) ((scalarMatrix M b).mulVec c) =
      ∑ i : Fin n, ∑ j : Fin n,
        inner Complex (M i j (∑ q : β, star (c (j, q)) • b q))
          (∑ p : β, star (c (i, p)) • b p) := by sorry
