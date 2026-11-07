-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:33.266005+00:00
-- url     : https://prove2.me/theorems/4ace6b69-1d57-426d-95fa-9c6605bfba03
-- title:
--   Spherical Hecke: rank Three Fundamental Hecke Alg Equiv apply
-- statement:
--   The Spherical Hecke construction uses the rank Three Fundamental Hecke Alg Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L2376-L2381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L2376-L2381

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
    (k : Type u) [Field k] [Finite k]
    (p : MvPolynomial (Fin 2) ℂ) :
    rankThreeFundamentalHeckeAlgEquiv k p =
      rankThreeFundamentalHeckeEval k p := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
