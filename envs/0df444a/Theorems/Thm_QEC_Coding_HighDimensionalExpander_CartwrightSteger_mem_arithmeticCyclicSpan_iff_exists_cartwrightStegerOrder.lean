-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticCyclicSpan_iff_exists_cartwrightStegerOrder
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticCyclicSpan_iff_exists_cartwrightStegerOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:09:31.336422+00:00
-- url     : https://prove2.me/theorems/ee018910-5d65-4d79-9759-e3578e163079
-- title:
--   Cartwright Steger: mem arithmetic Cyclic Span iff exists cartwright Steger Order
-- statement:
--   The explicit arithmetic cyclic span is exactly the image of the
--   construction-owned Cartwright--Steger order in the global cyclic algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L497-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L497-L505

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticCyclicSpan_iff_exists_cartwrightStegerOrder
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    x ∈ arithmeticCyclicSpan P r ↔
      ∃ y : CartwrightStegerOrder P r,
        cartwrightStegerOrderToCyclicAlgebra P r y = x := by sorry
