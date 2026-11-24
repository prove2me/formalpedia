-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_detB
-- name    : PositivityTheory.ThKG.Std.detB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:58.388877+00:00
-- url     : https://prove2.me/theorems/473475cf-dd4f-498c-8b34-d5d827fa2e44
-- title:
--   Std: det B
-- statement:
--   The Std construction uses the det B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L16-L29

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

theorem PositivityTheory.ThKG.Std.detB {b : ℕ} (N : Matrix (Fin (b + 2)) (Fin (b + 2)) k) (h0 : ∀ j, j ≠ Fin.last _ → N 0 j = 0)
    (h1 : ∀ i, N (mid i) 0 = 0) : N.det = -N 0 (Fin.last _) * N (Fin.last _) 0 * (N.submatrix mid mid).det := by sorry
