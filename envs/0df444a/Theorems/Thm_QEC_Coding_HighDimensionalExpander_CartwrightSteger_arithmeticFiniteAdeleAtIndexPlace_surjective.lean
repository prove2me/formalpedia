-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleAtIndexPlace_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAtIndexPlace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:11:21.572382+00:00
-- url     : https://prove2.me/theorems/7e1314cf-525a-4dec-aa3d-d7ba7423092d
-- title:
--   Cartwright Steger: arithmetic Finite Adele At Index Place surjective
-- statement:
--   Evaluation of the arithmetic finite adeles at the selected abstract
--   adic place is onto, by the explicit one-place supported section.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1876-L1881
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1876-L1881

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAtIndexPlace_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (arithmeticFiniteAdeleAtIndexPlace P r level) := by sorry
