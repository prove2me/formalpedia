-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_connecting__restrict_f013bc8c52ad
-- name    : P2M_GlobalTheory_Flasque_connecting__restrict_f013bc8c52ad
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:24.129931+00:00
-- url     : https://prove2.me/theorems/d1b2b61a-e006-4423-aad3-3a46cbb35b75
-- title:
--   P2 M Global Theory Flasque connecting  restrict f013bc8c52ad: P2 M Global Theory Flasque connecting  restrict f013bc8c52ad
-- statement:
--   The P2 M Global Theory Flasque connecting  restrict f013bc8c52ad construction uses the P2 M Global Theory Flasque connecting  restrict f013bc8c52ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L196-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L196-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

theorem P2M_GlobalTheory_Flasque_connecting__restrict_f013bc8c52ad {V U : C} (i : V ⟶ U) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hS V (S.X₃.obj.map i.op s) =
      (S.X₁.cohomologyPresheaf 1).map i.op (connecting₀ hS U s) := by sorry

alias «GlobalTheory».«Flasque».«connecting₀_restrict» := P2M_GlobalTheory_Flasque_connecting__restrict_f013bc8c52ad
