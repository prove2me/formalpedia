-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_exists_haar
-- name    : PositivityTheory.ThKG.Fub.exists_haar
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:47.717305+00:00
-- url     : https://prove2.me/theorems/f6698600-48d1-4004-a260-f408ebe66ace
-- title:
--   Fub: exists haar
-- statement:
--   The Fub construction uses the exists haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L67-L72

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

theorem PositivityTheory.ThKG.Fub.exists_haar (S : Subgroup G) (hS : IsClosed (S : Set G)) (U : Set G) (h1 : (1 : G) ∈ U)
    (hc : IsCompact {x : S | x.1 ∈ U}) (ho : IsOpen {x : S | x.1 ∈ U}) :
    ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1 := by sorry
