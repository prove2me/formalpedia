-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_sandwich
-- name    : PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.sandwich
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:34.224067+00:00
-- url     : https://prove2.me/theorems/44f9ccae-c0c9-40c4-9cf3-b43d2b50ecae
-- title:
--   Determinant Monotonicity: sandwich
-- statement:
--   The Determinant Monotonicity construction uses the sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/DetMono.lean#L22-L24

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

theorem PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.sandwich {j : ℕ} (y X : Matrix (Fin j) (Fin j) ℂ) (v : Fin j → ℂ) :
    star v ⬝ᵥ ((yᴴ * X * y) *ᵥ v) = star (y *ᵥ v) ⬝ᵥ (X *ᵥ (y *ᵥ v)) := by sorry
