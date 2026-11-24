-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_nsq_ofReal
-- name    : PI.PolynomialProperness.CoreW.nsq_ofReal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:27.774483+00:00
-- url     : https://prove2.me/theorems/4060e3d8-227c-4a85-8e62-8a6a8c9640f0
-- title:
--   Core W: nsq of Real
-- statement:
--   The Core W construction uses the nsq of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L46-L47

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

theorem PI.PolynomialProperness.CoreW.nsq_ofReal {n : ℕ} (x : Fin n → ℂ) : ((nsq x : ℝ) : ℂ) = star x ⬝ᵥ x := by sorry
