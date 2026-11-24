-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_ext_off
-- name    : PositivityTheory.ThKG.Std.ext_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:31.132793+00:00
-- url     : https://prove2.me/theorems/be46d9e0-131c-4833-9d65-186b18c512d9
-- title:
--   Std: ext off
-- statement:
--   The Std construction uses the ext off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L63-L64

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

theorem PositivityTheory.ThKG.Std.ext_off (y : Matrix (Fin n₁) (Fin d₁) k) {i j} (h : (∀ i', i ≠ jr i') ∨ ∀ j', j ≠ jc j') : ext jr jc y i j = 0 := by sorry
