-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_indexCompletedBaseArithmeticEval
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_indexCompletedBaseArithmeticEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:45:11.119904+00:00
-- url     : https://prove2.me/theorems/1b75a022-5f47-470c-b9f5-2e31b18278bd
-- title:
--   Cartwright Steger: dense Range index Completed Base Arithmetic Eval
-- statement:
--   The actual base S-arithmetic ring is dense in the selected power-series
--   chart.  This uses the proved coefficient-by-coefficient lifts, so it does not
--   import a density certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5247-L5261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L5247-L5261

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
open scoped PowerSeries.WithPiTopology Topology WithZeroTopology Multiplicative
open MonoidWithZeroHom.ValueGroup₀
open Filter
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_indexCompletedBaseArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (indexCompletedBaseArithmeticEval P r level) := by sorry
