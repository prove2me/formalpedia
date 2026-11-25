-- Prove2me | Theorems.Thm_PI_VolStabW_meas_cntN
-- name    : PI.VolStabW.meas_cntN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:43:19.008646+00:00
-- url     : https://prove2.me/theorems/3652393d-e497-491b-a329-c8ed279eeb81
-- title:
--   Vol Stab W: meas cnt N
-- statement:
--   The Vol Stab W construction uses the meas cnt N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L102-L106

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

theorem PI.VolStabW.meas_cntN (Γ : Subgroup G) [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    Measurable (cntN Γ A) := by sorry
