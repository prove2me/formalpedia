-- Prove2me | Theorems.Thm_PI_VolStabSW_lint_mul_right
-- name    : PI.VolStabSW.lint_mul_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:39.693995+00:00
-- url     : https://prove2.me/theorems/1b4106da-999f-5302-8138-8a102b6f55d9
-- title:
--   Vol Stab SW: lint mul right
-- statement:
--   The Vol Stab SW construction uses the lint mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L81-L86

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

theorem PI.VolStabSW.lint_mul_right {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f : G → ℝ≥0∞) (r : G) : ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f g ∂μ := by sorry
