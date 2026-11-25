-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_measure_split
-- name    : PositivityTheory.SiegelWeilFormula.KFock.measure_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:07.365349+00:00
-- url     : https://prove2.me/theorems/47249ba5-c327-4812-9cb4-6af17b7e37c9
-- title:
--   KFock: measure split
-- statement:
--   The KFock construction uses the measure split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L22-L29

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

theorem PositivityTheory.SiegelWeilFormula.KFock.measure_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ c : NNReal, 0 < c ∧ ν = c • Measure.map Φ (la.prod mu) := by sorry
