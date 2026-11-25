-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_star_dot_self
-- name    : PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.star_dot_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:10.344538+00:00
-- url     : https://prove2.me/theorems/eaeb7a0b-4ccb-4830-8155-fc8eddaa59d8
-- title:
--   Determinant Monotonicity: star dot self
-- statement:
--   The Determinant Monotonicity construction uses the star dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

theorem PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.star_dot_self {n : ℕ} (w : Fin n → ℂ) : star w ⬝ᵥ w = ((nsq w : ℝ) : ℂ) := by sorry
