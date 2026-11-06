-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceRightRaw_trace_pairing
-- name    : QEC.Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:55.759093+00:00
-- url     : https://prove2.me/theorems/badb3d75-6792-4b97-b37b-5a7bf9fc2dec
-- title:
--   Finite Matrix Entropy: partial Trace Right Raw trace pairing
-- statement:
--   Concrete right partial-trace pairing for the repository's raw contraction
--   semantics.  It is the finite adjoint relation used to move a marginal
--   logarithm back onto the bipartite operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L712-L752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L712-L752

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {beta : Type u} [Fintype beta]
    (b : OrthonormalBasis beta Complex K) (A : Operator (CompositeSystem H K))
    (X : Operator H) :
    LinearMap.trace Complex H (((partialTraceRightRaw H K) A).comp X) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) := by sorry
