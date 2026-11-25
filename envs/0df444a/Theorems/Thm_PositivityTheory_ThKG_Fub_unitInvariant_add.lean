-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_unitInvariant_add
-- name    : PositivityTheory.ThKG.Fub.unitInvariant_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:56.399057+00:00
-- url     : https://prove2.me/theorems/6a1ebdd3-8f67-556e-9551-16e3393f07b6
-- title:
--   Fub: unit Invariant add
-- statement:
--   The Fub construction uses the unit Invariant add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L237-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L237-L245

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

theorem PositivityTheory.ThKG.Fub.unitInvariant_add {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) (x : Aˣ) :
    unitP (a + b) x = unitP a x * unitP b x := by sorry
