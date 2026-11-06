-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_ratFunc
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_ratFunc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:48.764083+00:00
-- url     : https://prove2.me/theorems/6629f08b-7daa-4972-95f8-e7e26b9862de
-- title:
--   Differential: global Simple Pole Residue Sum rat Func
-- statement:
--   The finite global traced-residue sum of every nonzero globally
--   simple-pole rational differential `f dX` vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/GlobalResidue.lean#L59-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/GlobalResidue.lean#L59-L148

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_ratFunc
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole (k := k) (F := RatFunc k)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        homega = 0 := by sorry
