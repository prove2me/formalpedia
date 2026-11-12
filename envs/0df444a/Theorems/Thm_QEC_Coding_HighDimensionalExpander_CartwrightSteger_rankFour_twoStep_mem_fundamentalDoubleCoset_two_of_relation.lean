-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:02:32.381025+00:00
-- url     : https://prove2.me/theorems/4bef6ca2-06f6-49bb-acee-57bd6ec83e59
-- title:
--   Cartwright Steger: rank Four two Step mem fundamental Double Coset two of relation
-- statement:
--   The Cartwright Steger construction uses the rank Four two Step mem fundamental Double Coset two of relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L266-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L266-L350

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
    (P : BasePrime)
    (a b c d : BuildingCartwrightStegerLattice P .four)
    (ha : a.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hb : b.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hc : c.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hd : d.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hprod : ((a * b) * c) * d = 1) :
    (a * b).1 ∈ fundamentalDoubleCoset (BaseField P) 4 2 := by sorry
