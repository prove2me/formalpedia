-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_prod_mid
-- name    : PositivityTheory.ThKG.Std.prod_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:02:18.838795+00:00
-- url     : https://prove2.me/theorems/34f7ea72-c4e3-4e73-bfba-734154829f68
-- title:
--   Std: prod mid
-- statement:
--   The Std construction uses the prod mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L92-L103

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

theorem PositivityTheory.ThKG.Std.prod_mid (hr : Function.Injective jr) (hc : Function.Injective jc) {e : Fin n → Fin d} {e₁ : Fin n₁ → Fin d₁}
    (he : ∀ j, jc j ∈ Set.range e ↔ j ∈ Set.range e₁) {P : Finset (Fin n × Fin d)} (hP : ∀ i j, (jr i, jc j) ∉ P)
    (y : Matrix (Fin n₁) (Fin d₁) k) :
    ∏ p : Fin n × Fin d, (if p ∈ P then 1 else ind (rad ϖ c e p.2) (ext jr jc y p.1 p.2)) =
      ∏ p : Fin n₁ × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2) := by sorry
