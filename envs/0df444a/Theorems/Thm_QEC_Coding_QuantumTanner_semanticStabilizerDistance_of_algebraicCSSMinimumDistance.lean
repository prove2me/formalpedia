-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_of_algebraicCSSMinimumDistance
-- name    : QEC.Coding.QuantumTanner.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:28:54.383074+00:00
-- url     : https://prove2.me/theorems/acda5929-acfc-4988-b521-eb8b61fe3ef1
-- title:
--   Quantum Tanner: semantic Stabilizer Distance of algebraic CSSMinimum Distance
-- statement:
--   An attained minimum over the union of the two nontrivial algebraic CSS
--   sectors is the semantic Pauli distance of the source-valid stabilizer built
--   from the same parity checks.  This form is the one produced by the Quantum
--   Tanner global-distance argument; unlike the sectorwise API, it does not assume
--   that each logical sector is separately nonempty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8693-L8790
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8693-L8790

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v

theorem QEC.Coding.QuantumTanner.semanticStabilizerDistance_of_algebraicCSSMinimumDistance
    {iota kappaP kappaQ : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappaP] [Fintype kappaQ]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p)
        (parityCheckRow Q q) = 0)
    {distance : Nat}
    (hDistance : AlgebraicCSSMinimumDistance
      (parityCheckRowCode Q)
      (parityCheckRowCode P) distance) :
    StabilizerCode.SemanticStabilizerDistance
      (PauliSymplectic.binaryCSSSourceValidStabilizerOfParityChecks
        P Q horth) distance := by sorry
