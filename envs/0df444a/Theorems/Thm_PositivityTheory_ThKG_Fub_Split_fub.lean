-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_Split_fub
-- name    : PositivityTheory.ThKG.Fub.Split.fub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:44:27.332707+00:00
-- url     : https://prove2.me/theorems/8fef9ffe-ea32-41ba-8226-ffaed031f5a3
-- title:
--   Split: fub
-- statement:
--   The Split construction uses the fub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L39-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L39-L65

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}

theorem PositivityTheory.ThKG.Fub.Split.fub (h : Split S A B p q) (μ : Measure S) (α : Measure A) (β : Measure B) [μ.IsHaarMeasure] [α.IsHaarMeasure]
    [β.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ f g : G → ℂ, Integrable (fun a : A => f a) α → Integrable (fun b : B => g b) β →
        Integrable (fun x : S => f (p x) * g (q x)) μ ∧
          ∫ x : S, f (p x) * g (q x) ∂μ = c * ((∫ a : A, f a ∂α) * ∫ b : B, g b ∂β)) ∧
      ∀ U : Set G, MeasurableSet U → (∀ g ∈ S, g ∈ U ↔ p g ∈ U ∧ q g ∈ U) →
        μ {x | x.1 ∈ U} = c * (α {x | x.1 ∈ U} * β {x | x.1 ∈ U}) := by sorry
