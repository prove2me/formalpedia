-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_cyclicAlgebraNormOne_with_finite_offTarget_denominators
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_with_finite_offTarget_denominators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:16:07.416519+00:00
-- url     : https://prove2.me/theorems/bb92ee68-d237-478d-b04d-6e6206b0dc9e
-- title:
--   Cartwright Steger: exists cyclic Algebra Norm One with finite off Target denominators
-- statement:
--   For every finite special-linear target there is a global rational
--   norm-one approximant with finite denominator support disjoint from the
--   selected congruence place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6770-L6786
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6770-L6786

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_with_finite_offTarget_denominators
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ∃ u : CyclicAlgebraNormOne P r,
      cyclicAlgebraNormOneToIndexLocal P r level u ∈
          indexLocalNormOneFiniteTargetNeighborhood P r level g ∧
        (cyclicAlgebraNormOneDenominatorPlaces P r u).Finite ∧
        indexCongruencePlace P r level ∉
          cyclicAlgebraNormOneDenominatorPlaces P r u := by sorry
