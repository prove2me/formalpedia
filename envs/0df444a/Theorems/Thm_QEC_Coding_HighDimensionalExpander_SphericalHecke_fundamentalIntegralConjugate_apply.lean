-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:00.109341+00:00
-- url     : https://prove2.me/theorems/b8d5ac52-1887-4e90-8124-7a7d26b6864b
-- title:
--   Spherical Hecke: fundamental Integral Conjugate apply
-- statement:
--   The Spherical Hecke construction uses the fundamental Integral Conjugate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L291-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L291-L303

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_apply
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) (i j : Fin d) :
    fundamentalIntegralConjugate k d r g i j =
      (if i.val < r then ((uniformizerUnit k)⁻¹ : LocalFunctionField k) else 1) *
        integerEmbedding k (g i j) *
      (if j.val < r then (uniformizerUnit k : LocalFunctionField k) else 1) := by sorry
