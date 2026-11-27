-- Prove2me | Theorems.Thm_PI_VolStabSW_meas_cntN
-- name    : PI.VolStabSW.meas_cntN
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:11.112727+00:00
-- url     : https://prove2.me/theorems/61340fd9-0cd5-4711-b0bd-710ccb7a980d
-- title:
--   Vol Stab SW: meas cnt N
-- statement:
--   The Vol Stab SW construction uses the meas cnt N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L107-L110

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]

theorem PI.VolStabSW.meas_cntN (Γ : Subgroup G) [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    Measurable (cntN Γ A) := by sorry
