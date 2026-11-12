-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_copies_distinct
-- name    : QEC.Coding.BDL26NativeTriangleColors.copies_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:38:48.186314+00:00
-- url     : https://prove2.me/theorems/71e99f8b-9abe-42f6-8d4d-95d3e4ac67c7
-- title:
--   BDL26 Native Triangle Colors: copies distinct
-- statement:
--   Distinct copy labels remain distinct rows, irrespective of image geometry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L645-L650
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L645-L650

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleColors.copies_distinct (S : OddScale) (n : ℕ) (f : (P S n).Face) :
    nativeRow S n (f,0)≠nativeRow S n (f,1) := by sorry
