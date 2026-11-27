-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Flasque_isFlasque_injectiveShortComplex_X__4b84a5ce729c
-- name    : P2M_GlobalTheory_Flasque_isFlasque_injectiveShortComplex_X__4b84a5ce729c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:37.075833+00:00
-- url     : https://prove2.me/theorems/351e1ac2-adaa-4da7-855e-dcd703cf45fd
-- title:
--   P2 M Global Theory Flasque is Flasque injective Short Complex X  4b84a5ce729c: P2 M Global Theory Flasque is Flasque injective Short Complex X  4b84a5ce729c
-- statement:
--   The P2 M Global Theory Flasque is Flasque injective Short Complex X  4b84a5ce729c construction uses the P2 M Global Theory Flasque is Flasque injective Short Complex X  4b84a5ce729c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L298-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L298-L300

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
variable {X : TopCat.{u}}

theorem P2M_GlobalTheory_Flasque_isFlasque_injectiveShortComplex_X__4b84a5ce729c (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (injectiveShortComplex F).X₃.IsFlasque := by sorry

alias «GlobalTheory».«Flasque».«isFlasque_injectiveShortComplex_X₃» := P2M_GlobalTheory_Flasque_isFlasque_injectiveShortComplex_X__4b84a5ce729c
