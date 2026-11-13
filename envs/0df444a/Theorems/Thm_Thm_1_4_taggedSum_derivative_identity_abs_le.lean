-- Prove2me | Theorems.Thm_Thm_1_4_taggedSum_derivative_identity_abs_le
-- name    : Thm_1_4.taggedSum_derivative_identity_abs_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:28:50.326877+00:00
-- url     : https://prove2.me/theorems/7eea4114-86ab-4d27-8348-031edafbbe92
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.taggedSum_derivative_identity_abs_le
-- statement:
--   Source theorem `Thm_1_4.taggedSum_derivative_identity_abs_le` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem taggedSum_derivative_identity_abs_le {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by sorry

end Thm_1_4
