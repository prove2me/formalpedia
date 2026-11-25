-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_mx_mul_le
-- name    : PI.PolynomialProperness.GN.mx_mul_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:56.239686+00:00
-- url     : https://prove2.me/theorems/624172d3-d5f6-4965-a4e7-50d3d3bcb9df
-- title:
--   GN: mx mul le
-- statement:
--   The GN construction uses the mx mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L199-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L199-L211

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

theorem PI.PolynomialProperness.GN.mx_mul_le {m : ℕ} (A B' : Matrix (Fin m) (Fin m) ℂ) :
    C2.mx (A * B') ≤ m * C2.mx A * C2.mx B' := by sorry
