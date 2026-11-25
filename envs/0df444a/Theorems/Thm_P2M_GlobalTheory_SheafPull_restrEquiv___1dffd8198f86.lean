-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafPull_restrEquiv___1dffd8198f86
-- name    : P2M_GlobalTheory_SheafPull_restrEquiv___1dffd8198f86
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:45.934893+00:00
-- url     : https://prove2.me/theorems/a9ff8f60-f23f-53ec-bded-fcb76b9b3b15
-- title:
--   P2 M Global Theory Sheaf Pull restr Equiv   1dffd8198f86: P2 M Global Theory Sheaf Pull restr Equiv   1dffd8198f86
-- statement:
--   The P2 M Global Theory Sheaf Pull restr Equiv   1dffd8198f86 construction uses the P2 M Global Theory Sheaf Pull restr Equiv   1dffd8198f86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L159-L163

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
variable {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j)

theorem P2M_GlobalTheory_SheafPull_restrEquiv___1dffd8198f86 {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (n : ℕ) (V : Opens Y)
    (x : Sheaf.H'.{w} S.X₃ n (hj.functor.obj V)) :
    restrEquiv.{w, w'} hj S.X₁ (n + 1) V (δ hS n _ x) =
      δ (shortExact_map_restr hj hS) n V (restrEquiv.{w, w'} hj S.X₃ n V x) := by sorry

alias «GlobalTheory».«SheafPull».«restrEquiv_δ» := P2M_GlobalTheory_SheafPull_restrEquiv___1dffd8198f86
