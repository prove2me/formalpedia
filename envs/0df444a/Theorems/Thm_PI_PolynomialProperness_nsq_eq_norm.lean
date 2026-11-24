-- Prove2me | Theorems.Thm_PI_PolynomialProperness_nsq_eq_norm
-- name    : PI.PolynomialProperness.nsq_eq_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:38:11.707484+00:00
-- url     : https://prove2.me/theorems/e1c4e7c1-4a02-4c2f-bd27-3491452c1607
-- title:
--   Polynomial Properness: nsq eq norm
-- statement:
--   The Polynomial Properness construction uses the nsq eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/NsqMulVecLe.lean#L23-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.nsq_eq_norm {n : ℕ} (x : Fin n → ℂ) : nsq x = ∑ i, ‖x i‖ ^ 2 := by sorry
