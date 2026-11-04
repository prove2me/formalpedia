-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedColumnEnumeration_equiv_symm_digit
-- name    : ThreeSum.TernaryPairedColumnEnumeration.equiv_symm_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:37.805119+00:00
-- url     : https://prove2.me/theorems/ce84ddaa-d3f5-4f3e-811b-aaa8447ff57c
-- title:
--   Ternary Paired Column Enumeration: equiv symm digit
-- statement:
--   The Ternary Paired Column Enumeration construction uses the equiv symm digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedColumnEnumeration.lean#L20-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedColumnEnumeration.lean#L20-L30

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedColumnEnumeration
open TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.TernaryPairedColumnEnumeration.equiv_symm_digit (m Λ : ℕ) (i : Fin (Λ^width m)) (r : PairedIndex m) :
    ((equiv m Λ).symm i r).val =
      WeightEnumeration.digit Λ (width m) i.val (Fintype.equivFin (PairedIndex m) r).val := by sorry
