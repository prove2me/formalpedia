-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_fvec_sum_le
-- name    : PI.PolynomialProperness.GN.fvec_sum_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:36:22.098429+00:00
-- url     : https://prove2.me/theorems/3a2eab22-6061-5470-a1df-832db45369b4
-- title:
--   GN: fvec sum le
-- statement:
--   The GN construction uses the fvec sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L227-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L227-L236

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem PI.PolynomialProperness.GN.fvec_sum_le (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    ∑ i, ‖fvec k r z a i‖ ≤ 1 + ∑ i, ‖z i‖ := by sorry
