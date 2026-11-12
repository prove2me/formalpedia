-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_success_accounting
-- name    : QEC.Coding.BDL26NativeTriangleColors.row_success_accounting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:19:54.49019+00:00
-- url     : https://prove2.me/theorems/f6c73857-3179-4ec8-bd23-b21a902a6bdb
-- title:
--   BDL26 Native Triangle Colors: row success accounting
-- statement:
--   The BDL26 Native Triangle Colors construction uses the row success accounting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L220-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L220-L236

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.row_success_accounting {A : Type*} [DecidableEq A] (L : List (AtlasRow A))
    (c : Code) (v : Triple A)
    (h : (BDL26NativeSupportMetadata.atlasReadQ c L).value=some v) :
    (colorRowQ L c).operations=(BDL26NativeSupportMetadata.atlasReadQ c L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.1 0 L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.2.1 1 L).operations+
      (fiberScanQ (2*c.owner+c.copy) v.2.2 2 L).operations+38 ∧
      (colorRowQ L c).allocations=9 := by sorry
