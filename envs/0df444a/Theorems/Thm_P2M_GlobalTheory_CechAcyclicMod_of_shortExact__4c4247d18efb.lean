-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CechAcyclicMod_of_shortExact__4c4247d18efb
-- name    : P2M_GlobalTheory_CechAcyclicMod_of_shortExact__4c4247d18efb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:13:05.037964+00:00
-- url     : https://prove2.me/theorems/75725ce8-d2af-51d0-bc6f-d90cdcc961d9
-- title:
--   P2 M Global Theory Cech Acyclic Mod of short Exact  4c4247d18efb: P2 M Global Theory Cech Acyclic Mod of short Exact  4c4247d18efb
-- statement:
--   The P2 M Global Theory Cech Acyclic Mod of short Exact  4c4247d18efb construction uses the P2 M Global Theory Cech Acyclic Mod of short Exact  4c4247d18efb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L308-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L308-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}

theorem P2M_GlobalTheory_CechAcyclicMod_of_shortExact__4c4247d18efb {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : CechAcyclicMod V U S.X₁) (h₂ : CechAcyclicMod V U S.X₂) : CechAcyclicMod V U S.X₃ := by sorry

alias «GlobalTheory».«CechAcyclicMod».«of_shortExact₃» := P2M_GlobalTheory_CechAcyclicMod_of_shortExact__4c4247d18efb
