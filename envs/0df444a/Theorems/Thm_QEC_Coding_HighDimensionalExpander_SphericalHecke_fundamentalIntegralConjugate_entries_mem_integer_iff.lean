-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_entries_mem_integer_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_entries_mem_integer_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:01.503581+00:00
-- url     : https://prove2.me/theorems/d626c8be-3194-4fe4-9701-3e29e493eae6
-- title:
--   Spherical Hecke: fundamental Integral Conjugate entries mem integer iff
-- statement:
--   Entrywise integrality of the conjugate is exactly vanishing of the
--   upper-right residue block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L319-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L319-L363

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_entries_mem_integer_iff
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    (∀ i j, fundamentalIntegralConjugate k d r g i j ∈
      Valued.integer (LocalFunctionField k)) ↔
      UpperRightResidueZero k d r g := by sorry
