-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_exact_connecting__map_2f4556a98bdf
-- name    : P2M_GlobalTheory_Flasque_exact_connecting__map_2f4556a98bdf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:43.411334+00:00
-- url     : https://prove2.me/theorems/408a723d-9567-4f87-b8e3-587a199f5ca8
-- title:
--   P2 M Global Theory Flasque exact connecting  map 2f4556a98bdf: P2 M Global Theory Flasque exact connecting  map 2f4556a98bdf
-- statement:
--   The P2 M Global Theory Flasque exact connecting  map 2f4556a98bdf construction uses the P2 M Global Theory Flasque exact connecting  map 2f4556a98bdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L170-L178

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

theorem P2M_GlobalTheory_Flasque_exact_connecting__map_2f4556a98bdf (U : C) :
    Function.Exact (connecting₀ hS U)
      (((Sheaf.cohomologyPresheafFunctor J 1).map S.f).app (op U)) := by sorry

alias «GlobalTheory».«Flasque».«exact_connecting₀_map» := P2M_GlobalTheory_Flasque_exact_connecting__map_2f4556a98bdf
