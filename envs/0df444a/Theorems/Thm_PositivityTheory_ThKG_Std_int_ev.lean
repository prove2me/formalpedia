-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_int_ev
-- name    : PositivityTheory.ThKG.Std.int_ev
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:44.613267+00:00
-- url     : https://prove2.me/theorems/ee426713-d12a-51a0-b9f3-a70683b1fb0a
-- title:
--   Std: int ev
-- statement:
--   The Std construction uses the int ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L129-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L129-L152

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

theorem PositivityTheory.ThKG.Std.int_ev (hm : IsVol m) (hϖ : IsUnif ϖ) {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin n → Fin d}
    {e₁ : Fin n → Fin d₁} (he : ∀ i, jc (e₁ i) = e i) (j₀ : Fin d) (h0 : j₀ ∉ Set.range e) (h1 : ∀ j, j₀ ≠ jc j)
    (y : Matrix (Fin n) (Fin d₁) k) :
    ∫ Z, std ν ϖ c e (tm (cut (Finset.univ.filter fun p => p.2 = j₀) Z) + ext id jc y) * wt (Finset.univ.filter fun p => p.2 = j₀) Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ n * std ν ϖ c e₁ y := by sorry
