-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_std_mem
-- name    : PositivityTheory.ThKG.Std.std_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:59.581528+00:00
-- url     : https://prove2.me/theorems/595b1ea1-204e-4624-8306-b78237360256
-- title:
--   Std: std mem
-- statement:
--   The Std construction uses the std mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L83-L90

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
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
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}

theorem PositivityTheory.ThKG.Std.std_mem (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (e : Fin n → Fin d) :
    std ν ϖ c e ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by sorry
