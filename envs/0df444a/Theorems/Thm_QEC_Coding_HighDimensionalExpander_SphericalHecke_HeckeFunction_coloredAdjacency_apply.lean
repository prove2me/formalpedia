-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_coloredAdjacency_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.coloredAdjacency_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:02.059205+00:00
-- url     : https://prove2.me/theorems/035bc1ea-bb19-4631-aeaa-94c16d4a9b8a
-- title:
--   Hecke Function: colored Adjacency apply
-- statement:
--   The Hecke Function construction uses the colored Adjacency apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1242-L1257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1242-L1257

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
open QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.coloredAdjacency_apply
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : HeckeFunction k d) (x : HeckeGroup k d) :
    coloredAdjacency k d r f x =
      ∫ t in fundamentalDoubleCoset k d r,
        f (t⁻¹ * x) ∂(normalizedLocalHaarMeasure k d) := by sorry
