-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZ_actual_guard
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZ_actual_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:08:19.350338+00:00
-- url     : https://prove2.me/theorems/3eaaa390-b853-43ae-98c6-c6f58ea3288f
-- title:
--   BDL26 Canonical History Marks: local Z actual guard
-- statement:
--   The guard concerns the real base snapshot of a literal valid actual input;
--   its owner is intrinsically unparented even when that guard marks it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L38-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L38-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZ_actual_guard (S : OddScale) (n : Nat) (sigma : Input S n) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S)
    (h : (baseInput S n sigma).val (localZCoordinate S n x f) ≠ 0) :
    physicalNode S n 0 (localZ S x f) ∈ marks S n sigma ∧
      parent S 1 (localZ S x f) = none := by sorry
