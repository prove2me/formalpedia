-- Prove2me | Theorems.Thm_PI_VolStabW_lint_mul_right
-- name    : PI.VolStabW.lint_mul_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:23.036212+00:00
-- url     : https://prove2.me/theorems/d1310a15-81ab-52be-89fe-d4e5823bf8bb
-- title:
--   Vol Stab W: lint mul right
-- statement:
--   The Vol Stab W construction uses the lint mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L73-L81

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

theorem PI.VolStabW.lint_mul_right {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f : G → ℝ≥0∞) (r : G) : ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f g ∂μ := by sorry
