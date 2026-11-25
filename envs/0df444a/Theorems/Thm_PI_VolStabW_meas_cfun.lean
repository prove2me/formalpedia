-- Prove2me | Theorems.Thm_PI_VolStabW_meas_cfun
-- name    : PI.VolStabW.meas_cfun
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:43:16.576277+00:00
-- url     : https://prove2.me/theorems/6ef61490-dc8f-4ca9-bf4c-c2738e8eea5e
-- title:
--   Vol Stab W: meas cfun
-- statement:
--   The Vol Stab W construction uses the meas cfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L108-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs
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
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]

theorem PI.VolStabW.meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by sorry
