-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b
-- name    : P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:10.119732+00:00
-- url     : https://prove2.me/theorems/0a0aecab-10d1-4fa8-b709-6295056b6bd6
-- title:
--   P2 M Global Theory Sheaf Pull site Pull   e9f696f6870b: P2 M Global Theory Sheaf Pull site Pull   e9f696f6870b
-- statement:
--   The P2 M Global Theory Sheaf Pull site Pull   e9f696f6870b construction uses the P2 M Global Theory Sheaf Pull site Pull   e9f696f6870b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L213-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FreeYonedaHomEquivFreeToPullbackComp.lean#L213-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}

theorem P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} S.X₃ n V) :
    sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i (δ hS n V x) =
      δ hT n W (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i x) := by sorry

alias «GlobalTheory».«SheafPull».«sitePull_δ» := P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b
