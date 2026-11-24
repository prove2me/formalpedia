-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_split_prod
-- name    : PositivityTheory.ThKG.Std.split_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:58.575645+00:00
-- url     : https://prove2.me/theorems/ee7fe91b-aa10-4461-966e-c835fe493fcf
-- title:
--   Std: split prod
-- statement:
--   The Std construction uses the split prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L119-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L119-L127

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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}

theorem PositivityTheory.ThKG.Std.split_prod {e : Fin n → Fin d} (P : Finset (Fin n × Fin d)) (Y : Matrix (Fin n) (Fin d) k) (hY : ∀ p ∈ P, Y p.1 p.2 = 0)
    (Z : Fin n × Fin d → k) : (∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) ((tm (cut P Z) + Y) p.1 p.2)) * wt P Z =
      (∏ p : Fin n × Fin d, if p ∈ P then 1 else ind (rad ϖ c e p.2) (Y p.1 p.2)) *
        ∏ p : Fin n × Fin d, (if p ∈ P then ind (rad ϖ c e p.2) (Z p) else ind 1 (Z p)) := by sorry
