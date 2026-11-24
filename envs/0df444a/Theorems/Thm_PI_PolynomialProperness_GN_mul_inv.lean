-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_mul_inv
-- name    : PI.PolynomialProperness.GN.mul_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:55:02.500808+00:00
-- url     : https://prove2.me/theorems/3f904000-9784-4d72-8b32-5828ee7844ba
-- title:
--   GN: mul inv
-- statement:
--   The GN construction uses the mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L33-L34

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

theorem PI.PolynomialProperness.GN.mul_inv {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g * g⁻¹ = 1 := by sorry
