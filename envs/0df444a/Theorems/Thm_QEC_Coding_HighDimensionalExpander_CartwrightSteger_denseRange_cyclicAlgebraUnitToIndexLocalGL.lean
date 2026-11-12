-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_cyclicAlgebraUnitToIndexLocalGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraUnitToIndexLocalGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:47:34.967926+00:00
-- url     : https://prove2.me/theorems/8793dfd6-9ef3-4ae1-9c86-839b31845427
-- title:
--   Cartwright Steger: dense Range cyclic Algebra Unit To Index Local GL
-- statement:
--   Global units of the cyclic division algebra are dense in the selected
--   local general-linear group.  Additive density supplies a global algebra
--   point in every open matrix neighborhood of a local unit; openness of `GL`
--   and the division-algebra property turn that point into a genuine global
--   unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5535-L5568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5535-L5568

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraUnitToIndexLocalGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange
      (Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom) := by sorry
