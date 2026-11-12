-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:53:55.49668+00:00
-- url     : https://prove2.me/theorems/33c1c63e-de5f-41c8-aae3-7cde11399a90
-- title:
--   Cartwright Steger: index Congruence Place not mem cyclic Algebra Norm One Denominator Places
-- statement:
--   A global rational norm-one point lying in a selected finite-target
--   neighborhood has no denominator at the selected congruence place.  Its
--   remaining denominator support is therefore a finite set of other arithmetic
--   places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6720-L6765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6720-L6765

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (u : CyclicAlgebraNormOne P r)
    (hu : cyclicAlgebraNormOneToIndexLocal P r level u ∈
      indexLocalNormOneFiniteTargetNeighborhood P r level g) :
    indexCongruencePlace P r level ∉
      cyclicAlgebraNormOneDenominatorPlaces P r u := by sorry
