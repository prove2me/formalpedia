-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:53:42.069191+00:00
-- url     : https://prove2.me/theorems/cb4fcb66-145d-4213-bbcc-988b873b4647
-- title:
--   Cartwright Steger: index Completed Norm One Inner Form To Index Local of Integral Entries
-- statement:
--   The Cartwright Steger construction uses the index Completed Norm One Inner Form To Index Local of Integral Entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6457-L6467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6457-L6467

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    indexCompletedNormOneInnerFormToIndexLocal P r level
        (indexLocalNormOneToCompletedOfIntegralEntries P r level s hs) = s := by sorry
