-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_mem_part
-- name    : PositivityTheory.ThKG.Fub.mem_part
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:44.500188+00:00
-- url     : https://prove2.me/theorems/5129feba-30d5-4758-a209-0f80f1945045
-- title:
--   Fub: mem part
-- statement:
--   The Fub construction uses the mem part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L91-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L91-L91

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

theorem PositivityTheory.ThKG.Fub.mem_part {P : R → G →* G} {K : Subgroup G} {a : R} {g : G} : g ∈ part P K a ↔ g ∈ K ∧ P a g = g := by sorry
