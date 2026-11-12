-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_failure
-- name    : QEC.Coding.BDL26NativeTriangleColors.row_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:18:44.392792+00:00
-- url     : https://prove2.me/theorems/edca6a03-b8b7-460d-b1b6-f2d6f167edc7
-- title:
--   BDL26 Native Triangle Colors: row failure
-- statement:
--   The BDL26 Native Triangle Colors construction uses the row failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L208-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L208-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.row_failure {A : Type*} [DecidableEq A] (L : List (AtlasRow A)) (c : Code)
    (h : (BDL26NativeSupportMetadata.atlasReadQ c L).value=none) :
    (colorRowQ L c).value=(c,none) ∧
      (colorRowQ L c).operations=(BDL26NativeSupportMetadata.atlasReadQ c L).operations+24 ∧
      (colorRowQ L c).allocations=2 := by sorry
