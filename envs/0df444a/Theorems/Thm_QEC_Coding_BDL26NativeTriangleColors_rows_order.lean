-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_rows_order
-- name    : QEC.Coding.BDL26NativeTriangleColors.rows_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:24:05.516127+00:00
-- url     : https://prove2.me/theorems/376585ad-8ea8-4271-9602-24ff246c14a5
-- title:
--   BDL26 Native Triangle Colors: rows order
-- statement:
--   The BDL26 Native Triangle Colors construction uses the rows order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L254-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L254-L259

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.rows_order {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) :
    (colorRowsQ L).value.map Prod.fst=L.map Prod.fst := by sorry
