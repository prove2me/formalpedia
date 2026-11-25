-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CA_finish_bound
-- name    : PI.PolynomialProperness.CA.finish_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:59.171886+00:00
-- url     : https://prove2.me/theorems/b4800765-98b3-4064-8947-7bc32bdf94b3
-- title:
--   CA: finish bound
-- statement:
--   The CA construction uses the finish bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnitriangularInverseBoundOf.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnitriangularInverseBoundOf.lean#L30-L36

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

theorem PI.PolynomialProperness.CA.finish_bound {M C0 X A G : ℝ} (e : ℕ) (hm : M ≤ C0 * X ^ e) (hX : 0 ≤ X) (hXY : X ≤ A * G) :
    M ≤ max C0 0 * A ^ e * G ^ e := by sorry
