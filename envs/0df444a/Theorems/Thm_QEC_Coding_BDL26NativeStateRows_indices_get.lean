-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_get
-- name    : QEC.Coding.BDL26NativeStateRows.indices_get
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:39:27.026744+00:00
-- url     : https://prove2.me/theorems/909ebfb6-4c44-449d-a61f-240c6c0e4a45
-- title:
--   BDL26 Native State Rows: indices get
-- statement:
--   Reading addresses in generated order recovers the exact native code list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L156-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L156-L167

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem QEC.Coding.BDL26NativeStateRows.indices_get {A : Type*} (L : List A) :
    (indices L.length).map L.get=L := by sorry
