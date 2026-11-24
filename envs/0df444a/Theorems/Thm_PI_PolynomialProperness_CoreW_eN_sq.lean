-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sq
-- name    : PI.PolynomialProperness.CoreW.eN_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:38.414099+00:00
-- url     : https://prove2.me/theorems/abf0b3f3-18b8-44be-a557-3e40e8764b33
-- title:
--   Core W: e N sq
-- statement:
--   The Core W construction uses the e N sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L35-L37

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

theorem PI.PolynomialProperness.CoreW.eN_sq {n : ℕ} (x : Fin n → ℂ) : eN x ^ 2 = nsq x := by sorry
