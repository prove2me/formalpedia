-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixValueBounds_prefix_count_le_word_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:35.037976+00:00
-- url     : https://prove2.me/theorems/f46fb4e2-527f-4500-88f0-b19e6ee7e0fd
-- title:
--   Reporting Host Suffix Value Bounds: prefix count le word
-- statement:
--   The Reporting Host Suffix Value Bounds construction uses the prefix count le word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixValueBounds.lean#L38-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixValueBounds.lean#L38-L73

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixValueBounds
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
open scoped BigOperators
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word_w3sum_ac885d1 {h J k t : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word) :
    (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ≤ lim.word := by sorry
