-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:11:16.86319+00:00
-- url     : https://prove2.me/theorems/f1d85204-6dd7-4d33-b739-52e5a1916fd6
-- title:
--   Cartwright Steger: image preimage arithmetic Finite Adele Cyclic Integral Norm One Set
-- statement:
--   Exact image form of the arithmetic intersection: restricting the global
--   rational norm-one points to the adelic integral chart gives precisely the
--   finite-adelic image of the construction-owned integral norm-one inner form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1438-L1458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L1438-L1458

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r ''
        (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r) ⁻¹'
          ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r =
      Set.range (orderNormOneInnerFormToArithmeticFiniteAdeleNormOne P r) := by sorry
