-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:52.490213+00:00
-- url     : https://prove2.me/theorems/51e52d2c-b933-46bd-afd4-3963f2d902a8
-- title:
--   Hecke Function: star fundamental Hecke Function rank Four three
-- statement:
--   The Hecke Function construction uses the star fundamental Hecke Function rank Four three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1228-L1233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1228-L1233

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
    (k : Type u) [Field k] [Finite k] :
    star (fundamentalHeckeFunction k 4 3) =
      fundamentalHeckeFunction k 4 1 := by sorry
