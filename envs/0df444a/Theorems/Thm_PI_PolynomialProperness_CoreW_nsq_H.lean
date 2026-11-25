-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_nsq_H
-- name    : PI.PolynomialProperness.CoreW.nsq_H
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:08.351409+00:00
-- url     : https://prove2.me/theorems/0c3af3c8-6a56-51d7-9ec2-8470a74c2f93
-- title:
--   Core W: nsq H
-- statement:
--   The Core W construction uses the nsq H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L58-L61

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem PI.PolynomialProperness.CoreW.nsq_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : nsq (H *ᵥ v) = nsq v := by sorry
