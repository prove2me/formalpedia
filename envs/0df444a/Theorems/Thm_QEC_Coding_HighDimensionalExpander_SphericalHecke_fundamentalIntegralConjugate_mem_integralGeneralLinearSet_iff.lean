-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:20.531011+00:00
-- url     : https://prove2.me/theorems/3e6f890a-5492-4e87-9a3b-e2879e39d0ff
-- title:
--   Spherical Hecke: fundamental Integral Conjugate mem integral General Linear Set iff
-- statement:
--   Full invertible integrality of the conjugate, including its inverse,
--   is the two-sided residue block condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L386-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L386-L399

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    fundamentalIntegralConjugate k d r g ∈ integralGeneralLinearSet k d ↔
      UpperRightResidueZero k d r g ∧
        UpperRightResidueZero k d r g⁻¹ := by sorry
