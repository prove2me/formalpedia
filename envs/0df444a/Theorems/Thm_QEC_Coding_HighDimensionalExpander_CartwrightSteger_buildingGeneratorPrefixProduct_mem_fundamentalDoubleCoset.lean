-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:02:14.302735+00:00
-- url     : https://prove2.me/theorems/47937133-f343-4c40-9b62-1353184e7952
-- title:
--   Cartwright Steger: building Generator Prefix Product mem fundamental Double Coset
-- statement:
--   The Cartwright Steger construction uses the building Generator Prefix Product mem fundamental Double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L493-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L493-L603

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r)
    {color : Nat} (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    (buildingGeneratorPrefixProduct P r color u).1 ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by sorry
