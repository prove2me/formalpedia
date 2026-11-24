-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_mx_conjTranspose
-- name    : PI.PolynomialProperness.GN.mx_conjTranspose
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:00.281373+00:00
-- url     : https://prove2.me/theorems/edc8889b-0ad2-4656-a7a3-5ffd7e45346d
-- title:
--   GN: mx conj Transpose
-- statement:
--   The GN construction uses the mx conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L191-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L191-L197

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

theorem PI.PolynomialProperness.GN.mx_conjTranspose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : C2.mx Mᴴ = C2.mx M := by sorry
