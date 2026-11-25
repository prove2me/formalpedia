-- Prove2me | Theorems.Thm_PI_VolStabS_countable_subgroupOf
-- name    : PI.VolStabS.countable_subgroupOf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:19.814976+00:00
-- url     : https://prove2.me/theorems/2b233483-b6d4-4685-9e2b-8ea2d5a53b57
-- title:
--   Vol Stab S: countable subgroup Of
-- statement:
--   The Vol Stab S construction uses the countable subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L27-L34

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

theorem PI.VolStabS.countable_subgroupOf {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by sorry
