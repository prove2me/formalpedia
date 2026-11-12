-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:52:10.612853+00:00
-- url     : https://prove2.me/theorems/2066d183-79d4-46b6-a812-682e4edb388a
-- title:
--   Cartwright Steger: finite Special Linear To Index Local Norm One mem neighborhood
-- statement:
--   The Cartwright Steger construction uses the finite Special Linear To Index Local Norm One mem neighborhood property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5827-L5834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5827-L5834

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    finiteSpecialLinearToIndexLocalNormOne P r level g ∈
      indexLocalNormOneFiniteTargetNeighborhood P r level g := by sorry
