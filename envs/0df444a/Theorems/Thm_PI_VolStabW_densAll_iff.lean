-- Prove2me | Theorems.Thm_PI_VolStabW_densAll_iff
-- name    : PI.VolStabW.densAll_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:24.890947+00:00
-- url     : https://prove2.me/theorems/da6bd69f-7f33-434c-9ae1-60c2628ceefe
-- title:
--   Vol Stab W: dens All iff
-- statement:
--   The Vol Stab W construction uses the dens All iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibFour.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FibFour.lean#L22-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

theorem PI.VolStabW.densAll_iff (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν := by sorry
