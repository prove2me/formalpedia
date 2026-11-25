-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_transport
-- name    : PositivityTheory.ThKG.Fub.transport
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:50.2161+00:00
-- url     : https://prove2.me/theorems/4ba26edf-1b74-5621-b905-983414edcd55
-- title:
--   Fub: transport
-- statement:
--   The Fub construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L193-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L193-L201

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
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

theorem PositivityTheory.ThKG.Fub.transport {S S' : Subgroup G} (h : S = S') (mS : MeasurableSpace S) (hm : mS = borel S) (x : @Measure S mS) :
    ∃ x' : Measure S', (@Measure.IsHaarMeasure _ _ _ mS x → x'.IsHaarMeasure) ∧
      (∀ U : Set G, x' {y | y.1 ∈ U} = x {y | y.1 ∈ U}) ∧ ∀ f : G → ℂ,
        (Integrable (fun y : S' => f y) x' ↔ @Integrable _ _ _ _ mS (fun y : S => f y) x) ∧
          ∫ y : S', f y ∂x' = @integral _ _ _ _ mS x fun y : S => f y := by sorry
