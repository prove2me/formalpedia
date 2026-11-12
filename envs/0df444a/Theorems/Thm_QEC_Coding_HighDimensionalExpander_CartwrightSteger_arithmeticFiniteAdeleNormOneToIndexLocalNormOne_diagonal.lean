-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:53:17.630925+00:00
-- url     : https://prove2.me/theorems/47baac6a-8cc6-4ef6-89b0-3415f475ac48
-- title:
--   Cartwright Steger: arithmetic Finite Adele Norm One To Index Local Norm One diagonal
-- statement:
--   The adelic selected-place map agrees with the existing direct global
--   localization on every global reduced-norm-one point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6281-L6290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6281-L6290

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CyclicAlgebraNormOne P r) :
    arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level
        (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u) =
      cyclicAlgebraNormOneToIndexLocalNormOne P r level u := by sorry
