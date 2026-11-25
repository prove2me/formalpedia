-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_normSq_le_hs
-- name    : PI.PolynomialProperness.GN.normSq_le_hs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:45.438583+00:00
-- url     : https://prove2.me/theorems/cbf61718-8d0d-51f5-aaea-534d381d1d67
-- title:
--   GN: norm Sq le hs
-- statement:
--   The GN construction uses the norm Sq le hs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L138-L146

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

theorem PI.PolynomialProperness.GN.normSq_le_hs {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (i j : ι) :
    Complex.normSq (M i j) ≤ hs M := by sorry
