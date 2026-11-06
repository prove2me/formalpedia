-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceLeftRaw_trace_pairing
-- name    : QEC.Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:14.110075+00:00
-- url     : https://prove2.me/theorems/c57de4ed-6b69-4d27-9e88-d1a359148fa9
-- title:
--   Finite Matrix Entropy: partial Trace Left Raw trace pairing
-- statement:
--   Concrete left partial-trace pairing.  Together with
--   `partialTraceRightRaw_trace_pairing`, this supplies the two factor pairings
--   needed to move both marginal logarithms into a bipartite trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L767-L796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L767-L796

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

theorem QEC.Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) (Y : Operator K) :
    LinearMap.trace Complex K (((partialTraceLeftRaw H K) A).comp Y) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y)) := by sorry
