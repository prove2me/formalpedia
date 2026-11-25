-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_gN_sq
-- name    : PI.PolynomialProperness.GN.gN_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:20.489945+00:00
-- url     : https://prove2.me/theorems/8d1576a9-daca-4f69-8d31-27e0571ad52f
-- title:
--   GN: g N sq
-- statement:
--   The GN construction uses the g N sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L63-L64

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

theorem PI.PolynomialProperness.GN.gN_sq {k r : ℕ} (g : B.Mat k r) : B.gN g ^ 2 = hs g := by sorry
