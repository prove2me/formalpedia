-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_gN_eq
-- name    : PI.PolynomialProperness.GN.gN_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:53:29.098597+00:00
-- url     : https://prove2.me/theorems/e85360b8-f70b-4254-95af-725a68c73c05
-- title:
--   GN: g N eq
-- statement:
--   The GN construction uses the g N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L59-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L59-L59

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

theorem PI.PolynomialProperness.GN.gN_eq {k r : ℕ} (g : B.Mat k r) : B.gN g = Real.sqrt (hs g) := by sorry
