-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:06.295047+00:00
-- url     : https://prove2.me/theorems/a6686c19-c283-4a7d-b618-23bf92e6b2b9
-- title:
--   Hecke Function: star fundamental Hecke Function rank Four two
-- statement:
--   The Hecke Function construction uses the star fundamental Hecke Function rank Four two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1220-L1225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1220-L1225

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
    (k : Type u) [Field k] [Finite k] :
    star (fundamentalHeckeFunction k 4 2) =
      fundamentalHeckeFunction k 4 2 := by sorry
