-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:08.708553+00:00
-- url     : https://prove2.me/theorems/f3926130-8b4e-4088-b261-c6607ce35127
-- title:
--   Spherical Hecke: constant Coeff eq zero of uniformizer inv mul mem integer
-- statement:
--   Conversely, an integral quotient by the uniformizer forces vanishing
--   of the constant coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L250-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L250-L278

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f ∈
      Valued.integer (LocalFunctionField k)) :
    PowerSeries.constantCoeff f = 0 := by sorry
