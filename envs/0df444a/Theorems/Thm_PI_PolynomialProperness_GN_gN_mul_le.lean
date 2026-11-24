-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_gN_mul_le
-- name    : PI.PolynomialProperness.GN.gN_mul_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:51:13.219822+00:00
-- url     : https://prove2.me/theorems/6fc51690-e3ef-4e3a-a445-ace583a74877
-- title:
--   GN: g N mul le
-- statement:
--   The GN construction uses the g N mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L108-L110

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
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

theorem PI.PolynomialProperness.GN.gN_mul_le {k r : ℕ} (a b : B.Mat k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by sorry
