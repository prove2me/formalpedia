-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafPull_pushComparison___8033ec935204
-- name    : P2M_GlobalTheory_SheafPull_pushComparison___8033ec935204
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:12:24.342744+00:00
-- url     : https://prove2.me/theorems/d975b0ff-1ebd-4c46-9df1-38126a786502
-- title:
--   P2 M Global Theory Sheaf Pull push Comparison   8033ec935204: P2 M Global Theory Sheaf Pull push Comparison   8033ec935204
-- statement:
--   The P2 M Global Theory Sheaf Pull push Comparison   8033ec935204 construction uses the P2 M Global Theory Sheaf Pull push Comparison   8033ec935204 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L182-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PushComparisonBijectiveOfIsClosedEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' u
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
open SheafLES Flasque
variable {X Y : TopCat.{u}}
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)]
variable (f : Y ⟶ X)

theorem P2M_GlobalTheory_SheafPull_pushComparison___8033ec935204 {S : ShortComplex (AbSheaf Y)} (hS : S.ShortExact)
    (hS' : (S.map (push f)).ShortExact) (n : ℕ) (V : Opens X)
    (x : Sheaf.H'.{w} ((push f).obj S.X₃) n V) :
    pushComparison.{w, w'} f S.X₁ (n + 1) V (δ hS' n V x) =
      δ hS n _ (pushComparison.{w, w'} f S.X₃ n V x) := by sorry

alias «GlobalTheory».«SheafPull».«pushComparison_δ» := P2M_GlobalTheory_SheafPull_pushComparison___8033ec935204
