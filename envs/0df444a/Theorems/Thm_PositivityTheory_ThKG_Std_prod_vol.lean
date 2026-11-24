-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_prod_vol
-- name    : PositivityTheory.ThKG.Std.prod_vol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:52.486503+00:00
-- url     : https://prove2.me/theorems/a8ea377c-2911-4e19-9344-34cc410bf367
-- title:
--   Std: prod vol
-- statement:
--   The Std construction uses the prod vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L107-L117

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

theorem PositivityTheory.ThKG.Std.prod_vol (hm : IsVol m) (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {P : Finset (Fin n × Fin d)} {r : ℕ}
    (g : Fin r → Fin n × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e) :
    ∏ p : Fin n × Fin d, ∫ x, (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) ∂m = (((resCard k : ℂ) ^ c)⁻¹) ^ r := by sorry
