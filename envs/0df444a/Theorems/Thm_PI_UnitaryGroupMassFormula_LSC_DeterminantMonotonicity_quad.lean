-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_quad
-- name    : PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.quad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:21.238087+00:00
-- url     : https://prove2.me/theorems/64f3e6ee-a050-4efd-80df-37a5dfb48666
-- title:
--   Determinant Monotonicity: quad
-- statement:
--   The Determinant Monotonicity construction uses the quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L18-L20

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

theorem PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.quad {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (z : Fin j → ℂ) :
    star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = ((nsq (C *ᵥ z) : ℝ) : ℂ) := by sorry
