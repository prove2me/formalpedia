-- Prove2me | Theorems.Thm_PI_VolStabS_meas_cfun
-- name    : PI.VolStabS.meas_cfun
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:29.340415+00:00
-- url     : https://prove2.me/theorems/112d7219-58fa-5cf5-ab52-c23796c163d9
-- title:
--   Vol Stab S: meas cfun
-- statement:
--   The Vol Stab S construction uses the meas cfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L55-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]

theorem PI.VolStabS.meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by sorry
