-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integerEmbedding_mem_integer
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integerEmbedding_mem_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:01.503581+00:00
-- url     : https://prove2.me/theorems/d608b950-84b4-4a3f-a1ad-fa356a90515b
-- title:
--   Spherical Hecke: integer Embedding mem integer
-- statement:
--   The Spherical Hecke construction uses the integer Embedding mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L312-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L312-L315

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integerEmbedding_mem_integer
    (k : Type*) [Field k] (f : IntegerRing k) :
    integerEmbedding k f ∈ Valued.integer (LocalFunctionField k) := by sorry
