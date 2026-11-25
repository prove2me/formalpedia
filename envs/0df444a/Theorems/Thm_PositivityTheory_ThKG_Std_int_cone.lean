-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_int_cone
-- name    : PositivityTheory.ThKG.Std.int_cone
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:43.936035+00:00
-- url     : https://prove2.me/theorems/7c69aec3-45ff-5804-bb08-f67c602a0c14
-- title:
--   Std: int cone
-- statement:
--   The Std construction uses the int cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L154-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean#L154-L257

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

theorem PositivityTheory.ThKG.Std.int_cone (hm : IsVol m) (hϖ : IsUnif ϖ) {b : ℕ} {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin (b + 2) → Fin d}
    {e₁ : Fin b → Fin d₁} (hei : Function.Injective e) (he : ∀ i, jc (e₁ i) = e (mid i))
    (h0 : ∀ j, e 0 ≠ jc j) (h1 : ∀ j, e (Fin.last _) ≠ jc j) (P : Finset (Fin (b + 2) × Fin d)) (hP : ∀ i j, (mid i, jc j) ∉ P)
    (ha : (Fin.last _, e 0) ∈ P) (hb : (0, e (Fin.last _)) ∉ P)
    (hAB : ((∀ j, j ≠ Fin.last _ → (0, e j) ∉ P) ∧ ∀ i, (mid i, e 0) ∉ P) ∨
      ((∀ i, i ≠ 0 → (i, e (Fin.last _)) ∉ P) ∧ ∀ j, (Fin.last _, e (mid j)) ∉ P)) {r : ℕ}
    (g : Fin r → Fin (b + 2) × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e)
    (y : Matrix (Fin b) (Fin d₁) k) (s t : k) :
    ∫ Z, ψ (-(t * Z (Fin.last _, e 0))) * std ν ϖ c e (tm (cut P Z) + (ext mid jc y + single 0 (e (Fin.last _)) s)) * wt P Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ r * (dl ν s * gI m ψ ν t) * std ν ϖ c e₁ y := by sorry
