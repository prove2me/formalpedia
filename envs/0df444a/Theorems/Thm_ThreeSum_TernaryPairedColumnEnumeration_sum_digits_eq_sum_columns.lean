-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedColumnEnumeration_sum_digits_eq_sum_columns
-- name    : ThreeSum.TernaryPairedColumnEnumeration.sum_digits_eq_sum_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:11.368204+00:00
-- url     : https://prove2.me/theorems/bc6be68a-472e-4c24-8929-49e28e6bca1d
-- title:
--   Ternary Paired Column Enumeration: sum digits eq sum columns
-- statement:
--   The Ternary Paired Column Enumeration construction uses the sum digits eq sum columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedColumnEnumeration.lean#L32-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedColumnEnumeration.lean#L32-L44

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedColumnEnumeration
open TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.TernaryPairedColumnEnumeration.sum_digits_eq_sum_columns {R : Type*} [AddCommMonoid R] (m Λ : ℕ)
    (f : (PairedIndex m → ℕ) → R) :
    (∑ i ∈ Finset.range (Λ^width m), f (fun r =>
      WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val)) =
      ∑ cols : PairedIndex m → Fin Λ, f (fun r => (cols r).val) := by sorry
