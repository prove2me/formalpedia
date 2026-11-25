-- Prove2me | Theorems.Thm_PI_VolStabS_repO_mem
-- name    : PI.VolStabS.repO_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:12.659119+00:00
-- url     : https://prove2.me/theorems/c3524d28-aeb3-5f16-9b9b-23061d8af31b
-- title:
--   Vol Stab S: rep O mem
-- statement:
--   The Vol Stab S construction uses the rep O mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L43-L44

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

theorem PI.VolStabS.repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by sorry
