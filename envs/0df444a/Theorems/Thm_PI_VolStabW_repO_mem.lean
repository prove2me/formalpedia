-- Prove2me | Theorems.Thm_PI_VolStabW_repO_mem
-- name    : PI.VolStabW.repO_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:39.923744+00:00
-- url     : https://prove2.me/theorems/fe527e0b-87bf-4ff0-a0b7-be79cf83e9e8
-- title:
--   Vol Stab W: rep O mem
-- statement:
--   The Vol Stab W construction uses the rep O mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L90-L91

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

theorem PI.VolStabW.repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by sorry
