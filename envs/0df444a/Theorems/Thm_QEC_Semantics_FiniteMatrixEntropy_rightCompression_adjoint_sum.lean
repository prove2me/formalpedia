-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_rightCompression_adjoint_sum
-- name    : QEC.Semantics.FiniteMatrixEntropy.rightCompression_adjoint_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:50.494549+00:00
-- url     : https://prove2.me/theorems/9a5a8471-e1ec-404b-aa7f-4eeb203226e9
-- title:
--   Finite Matrix Entropy: right Compression adjoint sum
-- statement:
--   The adjoint Kraus sum of the repository's concrete right-compression formula
--   is extension by the identity on the traced-out factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L668-L705
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L668-L705

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

theorem QEC.Semantics.FiniteMatrixEntropy.rightCompression_adjoint_sum
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {beta : Type u} [Fintype beta]
    (b : OrthonormalBasis beta Complex K) (X : Operator H) :
    (∑ i : beta,
      (QEC.Locality.tensorRight H K (b i)).comp
        (X.comp (LinearMap.adjoint (QEC.Locality.tensorRight H K (b i))))) =
      TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K) := by sorry
