-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_dot_bound
-- name    : PI.PolynomialProperness.GN.dot_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:36:28.29636+00:00
-- url     : https://prove2.me/theorems/5898373a-e1f0-5a82-a194-18ba173ea14d
-- title:
--   GN: dot bound
-- statement:
--   The GN construction uses the dot bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L213-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L213-L225

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

theorem PI.PolynomialProperness.GN.dot_bound {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v w : ι → ℂ) {E : ℝ}
    (hE : ∀ i j, ‖M i j‖ ≤ E) :
    ‖star w ⬝ᵥ (M *ᵥ v)‖ ≤ (∑ i, ‖w i‖) * (∑ j, ‖v j‖) * E := by sorry
