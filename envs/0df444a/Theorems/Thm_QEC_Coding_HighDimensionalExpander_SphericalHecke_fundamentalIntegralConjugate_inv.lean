-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:12.603293+00:00
-- url     : https://prove2.me/theorems/44b9f920-27ab-4077-bb8d-63ea2b303b17
-- title:
--   Spherical Hecke: fundamental Integral Conjugate inv
-- statement:
--   The Spherical Hecke construction uses the fundamental Integral Conjugate inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L365-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L365-L371

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_inv
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    (fundamentalIntegralConjugate k d r g)⁻¹ =
      fundamentalIntegralConjugate k d r g⁻¹ := by sorry
