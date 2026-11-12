-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitToIndexPlace_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitToIndexPlace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:12:44.050816+00:00
-- url     : https://prove2.me/theorems/20f5413e-84be-4089-a576-a5a0afe30296
-- title:
--   Cartwright Steger: arithmetic Finite Adele Cyclic Unit To Index Place surjective
-- statement:
--   Every selected adic cyclic-algebra unit has a genuine finite-adelic
--   unit representative which is the identity away from that place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L2466-L2472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L2466-L2472

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitToIndexPlace_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleCyclicUnitToIndexPlace P r level) := by sorry
