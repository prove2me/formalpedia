-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerImage_unbounded_of_PSL_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerImage_unbounded_of_PSL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:55:11.112842+00:00
-- url     : https://prove2.me/theorems/e906ea4d-6038-4128-bf85-c77293acd226
-- title:
--   Cartwright Steger: index Cartwright Steger Image unbounded of PSL le
-- statement:
--   Once specialized strong approximation supplies `PSL` containment at
--   every selected congruence place, the actual finite Cartwright--Steger image
--   sizes are unbounded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L7267-L7277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L7267-L7277

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerImage_unbounded_of_PSL_le
    (P : BasePrime) (r : Rank)
    (hPSL : ∀ level,
      PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (bound : Nat) :
    ∃ level, bound <
      Nat.card (IndexCartwrightStegerImage P r level) := by sorry
