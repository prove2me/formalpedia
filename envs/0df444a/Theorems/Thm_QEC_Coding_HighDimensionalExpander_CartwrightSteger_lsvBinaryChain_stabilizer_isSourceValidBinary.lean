-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBinaryChain_stabilizer_isSourceValidBinary
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBinaryChain_stabilizer_isSourceValidBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:38:30.392044+00:00
-- url     : https://prove2.me/theorems/dfdbf150-9b27-4f1f-96c4-04c7aed8691f
-- title:
--   Cartwright Steger: lsv Binary Chain stabilizer is Source Valid Binary
-- statement:
--   The Cartwright Steger construction uses the lsv Binary Chain stabilizer is Source Valid Binary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1640-L1644
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1640-L1644

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBinaryChain_stabilizer_isSourceValidBinary
    (P : BasePrime) (r : Rank) (level p : Nat) :
    ((lsvBinaryChainAt P r level p).binaryCSSCode).stabilizer.IsSourceValidBinary := by sorry
