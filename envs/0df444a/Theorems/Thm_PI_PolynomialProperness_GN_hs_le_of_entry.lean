-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_hs_le_of_entry
-- name    : PI.PolynomialProperness.GN.hs_le_of_entry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:13.521798+00:00
-- url     : https://prove2.me/theorems/54bc0347-36b9-4132-9e65-49600a3e74f2
-- title:
--   GN: hs le of entry
-- statement:
--   The GN construction uses the hs le of entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L152-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L152-L162

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

theorem PI.PolynomialProperness.GN.hs_le_of_entry {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ c) : hs M ≤ (Fintype.card ι : ℝ) ^ 2 * c ^ 2 := by sorry
