-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexLocalNormOneFiniteTargetNeighborhood_entry_integral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexLocalNormOneFiniteTargetNeighborhood_entry_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:52:13.758539+00:00
-- url     : https://prove2.me/theorems/fcceb148-392d-4d62-8845-ea18b5a96ed7
-- title:
--   Cartwright Steger: index Local Norm One Finite Target Neighborhood entry integral
-- statement:
--   Every matrix entry of a point in a selected local finite-target
--   neighborhood is integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5838-L5872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5838-L5872

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexLocalNormOneFiniteTargetNeighborhood_entry_integral
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : s ∈ indexLocalNormOneFiniteTargetNeighborhood P r level g)
    (i j : Fin r.matrixRank) :
    ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j) ∈
        IndexCongruenceLocalIntegers P r level := by sorry
