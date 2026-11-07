-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_card_binaryLowWeightWords
-- name    : QEC.Coding.QuantumTanner.card_binaryLowWeightWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:23:31.282495+00:00
-- url     : https://prove2.me/theorems/a9220492-c957-46a8-9346-dac0b30ee753
-- title:
--   Quantum Tanner: card binary Low Weight Words
-- statement:
--   The exact cardinality of a binary Hamming ball of strict radius
--   `distance` on an arbitrary finite coordinate type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1124-L1136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L1124-L1136

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

theorem QEC.Coding.QuantumTanner.card_binaryLowWeightWords
    (ι : Type v) [Fintype ι] [DecidableEq ι] (distance : Nat) :
    Fintype.card (BinaryLowWeightWords ι distance) =
      ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card ι) weight := by sorry
