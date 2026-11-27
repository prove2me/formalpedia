-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_integral_split
-- name    : PositivityTheory.SiegelWeilFormula.KFock.integral_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:43.433882+00:00
-- url     : https://prove2.me/theorems/b2565f3c-0e42-4d1c-b7ab-0a7d30e267e3
-- title:
--   KFock: integral split
-- statement:
--   The KFock construction uses the integral split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L31-L40

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

theorem PositivityTheory.SiegelWeilFormula.KFock.integral_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G → ℂ, ∫ x, g x ∂ν = C * ∫ p, g (Φ p) ∂(la.prod mu) := by sorry
