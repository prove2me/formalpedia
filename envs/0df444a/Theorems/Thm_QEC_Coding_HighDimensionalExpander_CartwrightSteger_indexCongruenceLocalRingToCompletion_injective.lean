-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCongruenceLocalRingToCompletion_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruenceLocalRingToCompletion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:11:10.893203+00:00
-- url     : https://prove2.me/theorems/46d85201-a059-4709-8740-ea2d4b4555d0
-- title:
--   Cartwright Steger: index Congruence Local Ring To Completion injective
-- statement:
--   The concrete power-series chart is faithful on the genuine local ring;
--   it is therefore a completion chart rather than a quotient presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L2886-L2897
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L2886-L2897

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruenceLocalRingToCompletion_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCongruenceLocalRingToCompletion P r level) := by sorry
