-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_dl_add
-- name    : PositivityTheory.ThKG.Std.dl_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:07.104656+00:00
-- url     : https://prove2.me/theorems/921dbf2b-b761-45b9-844a-ee23d9c5fcc2
-- title:
--   Std: dl add
-- statement:
--   The Std construction uses the dl add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L54-L69

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

theorem PositivityTheory.ThKG.Std.dl_add (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (x : k) {t : k} (ht : valuation k t ≤ valuation k ((ϖ : k) ^ c)) :
    dl ν (x + t) = dl ν x := by sorry
