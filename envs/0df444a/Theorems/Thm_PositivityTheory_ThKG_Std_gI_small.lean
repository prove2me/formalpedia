-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_gI_small
-- name    : PositivityTheory.ThKG.Std.gI_small
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:08.132161+00:00
-- url     : https://prove2.me/theorems/53cf32ac-23e0-41fa-9617-bdb58ed54e25
-- title:
--   Std: g I small
-- statement:
--   The Std construction uses the g I small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L128-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L128-L145

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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}

theorem PositivityTheory.ThKG.Std.gI_small (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hν' : ¬ CondLE ϖ c ν) {y : k}
    (hy : valuation k (y * (ϖ : k) ^ c) ≤ 1) : gI m ψ ν y = 0 := by sorry
