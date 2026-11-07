-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:30.373168+00:00
-- url     : https://prove2.me/theorems/0b0900f3-01c1-4785-8904-4986aaba69c8
-- title:
--   Spherical Hecke: rank Four Fundamental Hecke Alg Equiv apply
-- statement:
--   The Spherical Hecke construction uses the rank Four Fundamental Hecke Alg Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L2393-L2398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L2393-L2398

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
    (k : Type u) [Field k] [Finite k]
    (p : MvPolynomial (Fin 3) ℂ) :
    rankFourFundamentalHeckeAlgEquiv k p =
      rankFourFundamentalHeckeEval k p := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
