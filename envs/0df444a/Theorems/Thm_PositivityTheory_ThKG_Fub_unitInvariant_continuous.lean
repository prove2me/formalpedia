-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_unitInvariant_continuous
-- name    : PositivityTheory.ThKG.Fub.unitInvariant_continuous
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:14.801411+00:00
-- url     : https://prove2.me/theorems/2fa6d387-9a81-46fe-a536-bb5568c0cd9a
-- title:
--   Fub: unit Invariant continuous
-- statement:
--   The Fub construction uses the unit Invariant continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L218-L221

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

theorem PositivityTheory.ThKG.Fub.unitInvariant_continuous {A : Type} [Ring A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul R A] {a : R}
    (h : a * a = a) : Continuous (unitP (A := A) a) := by sorry
