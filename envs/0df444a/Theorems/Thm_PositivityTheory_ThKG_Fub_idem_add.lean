-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Fub_idem_add
-- name    : PositivityTheory.ThKG.Fub.idem_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:15.667697+00:00
-- url     : https://prove2.me/theorems/f8ac21a7-13a4-45b5-b1e3-112e4a7d22fd
-- title:
--   Fub: idem add
-- statement:
--   The Fub construction uses the idem add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean#L234-L235

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

theorem PositivityTheory.ThKG.Fub.idem_add {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) : (a + b) * (a + b) = a + b := by sorry
