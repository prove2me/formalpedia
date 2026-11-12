-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:53:31.484635+00:00
-- url     : https://prove2.me/theorems/d659cf2c-662a-42be-a28e-b8dcb21e2486
-- title:
--   Cartwright Steger: exists cyclic Algebra Norm One mem index Local Finite Target Neighborhood
-- statement:
--   Every finite special-linear target has a global *rational* norm-one
--   point in its selected local congruence neighborhood.  This theorem makes no
--   integrality claim at the other arithmetic finite places; clearing precisely
--   those possible denominators is the remaining specialized strong-
--   approximation step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5879-L5892
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5879-L5892

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ∃ u : CyclicAlgebraNormOne P r,
      cyclicAlgebraNormOneToIndexLocal P r level u ∈
        indexLocalNormOneFiniteTargetNeighborhood P r level g := by sorry
