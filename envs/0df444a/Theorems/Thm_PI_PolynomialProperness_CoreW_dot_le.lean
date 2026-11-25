-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_dot_le
-- name    : PI.PolynomialProperness.CoreW.dot_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:45.8171+00:00
-- url     : https://prove2.me/theorems/a3c5c99b-c08c-4626-aedf-82f27f422ec2
-- title:
--   Core W: dot le
-- statement:
--   The Core W construction uses the dot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L39-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW

theorem PI.PolynomialProperness.CoreW.dot_le {n : ℕ} (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eN w * eN v := by sorry
