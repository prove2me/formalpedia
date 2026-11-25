-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_Xs
-- name    : PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_Xs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:53.796313+00:00
-- url     : https://prove2.me/theorems/01efcabb-838e-5d15-b657-09960af7b322
-- title:
--   Polynomial Degree Closure: pd Xs
-- statement:
--   The Polynomial Degree Closure construction uses the pd Xs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L75-L76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N : ℕ}

theorem PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_Xs (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g a b)) := by sorry
