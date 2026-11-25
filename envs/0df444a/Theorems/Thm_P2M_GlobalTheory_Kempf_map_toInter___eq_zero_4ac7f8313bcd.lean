-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd
-- name    : P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:25.18252+00:00
-- url     : https://prove2.me/theorems/525a4bc6-23d7-4dc2-a3fd-330787d8a13b
-- title:
--   P2 M Global Theory Kempf map to Inter   eq zero 4ac7f8313bcd: P2 M Global Theory Kempf map to Inter   eq zero 4ac7f8313bcd
-- statement:
--   The P2 M Global Theory Kempf map to Inter   eq zero 4ac7f8313bcd construction uses the P2 M Global Theory Kempf map to Inter   eq zero 4ac7f8313bcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L160-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L160-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES

theorem P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd (hS : S.ShortExact) {V W : Opens X} (s : S.X₃.obj.obj (op V))
    (t : S.X₂.obj.obj (op (V ⊓ W)))
    (ht : S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s) :
    map.{w} ((toInter AddCommGrpCat.{u} W).app S.X₁) 1 V
      (δ hS 0 V ((equivZero S.X₃ V).symm s)) = 0 := by sorry

alias «GlobalTheory».«Kempf».«map_toInter_δ_eq_zero» := P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd
