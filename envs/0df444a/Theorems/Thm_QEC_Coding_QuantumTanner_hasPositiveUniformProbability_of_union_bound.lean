-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_of_union_bound
-- name    : QEC.Coding.QuantumTanner.hasPositiveUniformProbability_of_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:23:00.032201+00:00
-- url     : https://prove2.me/theorems/c92397af-96ab-4937-ada8-64313a20f222
-- title:
--   Quantum Tanner: has Positive Uniform Probability of union bound
-- statement:
--   Finite union bound in the form needed by the LZ22 random local-code
--   argument.  If every failed sample lies in one of a finite family of bad events
--   and the sum of their cardinalities is smaller than the sample space, then the
--   simultaneous good event has positive uniform probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L787-L809
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L787-L809

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

theorem QEC.Coding.QuantumTanner.hasPositiveUniformProbability_of_union_bound
    {Ω : Type u} {J : Type v} [Fintype Ω] [Fintype J]
    (good : Ω → Prop) [DecidablePred good]
    (bad : J → Ω → Prop) [∀ j, DecidablePred (bad j)]
    (hcover : ∀ sample, ¬ good sample → ∃ j, bad j sample)
    (hcount : ∑ j, (eventFinset (bad j)).card < Fintype.card Ω) :
    HasPositiveUniformProbability good := by sorry
