-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_connecting__naturality_ca1f6f211643
-- name    : P2M_GlobalTheory_Flasque_connecting__naturality_ca1f6f211643
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:10.817854+00:00
-- url     : https://prove2.me/theorems/be6e6414-fc44-58d8-8386-ca612a1c9a3b
-- title:
--   P2 M Global Theory Flasque connecting  naturality ca1f6f211643: P2 M Global Theory Flasque connecting  naturality ca1f6f211643
-- statement:
--   The P2 M Global Theory Flasque connecting  naturality ca1f6f211643 construction uses the P2 M Global Theory Flasque connecting  naturality ca1f6f211643 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L187-L194

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

theorem P2M_GlobalTheory_Flasque_connecting__naturality_ca1f6f211643 {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (U : C) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hT U (φ.τ₃.hom.app (op U) s) =
      ((Sheaf.cohomologyPresheafFunctor J 1).map φ.τ₁).app (op U) (connecting₀ hS U s) := by sorry

alias «GlobalTheory».«Flasque».«connecting₀_naturality» := P2M_GlobalTheory_Flasque_connecting__naturality_ca1f6f211643
