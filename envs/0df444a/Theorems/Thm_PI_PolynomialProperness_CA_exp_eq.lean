-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CA_exp_eq
-- name    : PI.PolynomialProperness.CA.exp_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:59:07.531081+00:00
-- url     : https://prove2.me/theorems/99b7e61b-eeda-4cc1-be1f-df26f38c024d
-- title:
--   CA: exp eq
-- statement:
--   The CA construction uses the exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnitriangularInverseBoundOf.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnitriangularInverseBoundOf.lean#L38-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInverseBoundOf
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
open PI PI.PolynomialProperness PI.PolynomialProperness.CA

theorem PI.PolynomialProperness.CA.exp_eq (r : ℕ) : (r + 1 - 1) * (r + 1) = r * (r + 1) := by sorry
