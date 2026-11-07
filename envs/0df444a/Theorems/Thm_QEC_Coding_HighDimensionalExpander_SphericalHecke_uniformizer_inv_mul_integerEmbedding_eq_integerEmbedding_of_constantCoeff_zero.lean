-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:09.528505+00:00
-- url     : https://prove2.me/theorems/72d24bb9-1e47-4083-9b17-878c8be427d3
-- title:
--   Spherical Hecke: uniformizer inv mul integer Embedding eq integer Embedding of constant Coeff zero
-- statement:
--   If the residue of `f` vanishes, division by the uniformizer remains in
--   the valuation ring, with the displayed integral representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L234-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L234-L246

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : PowerSeries.constantCoeff f = 0) :
    ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f =
      integerEmbedding k (powerSeriesTail k f) := by sorry
