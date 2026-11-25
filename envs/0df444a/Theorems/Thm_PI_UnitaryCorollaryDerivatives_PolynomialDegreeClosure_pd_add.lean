-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_add
-- name    : PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:22.662931+00:00
-- url     : https://prove2.me/theorems/7e2cc30f-ec8e-50ad-85c3-c9708866c828
-- title:
--   Polynomial Degree Closure: pd add
-- statement:
--   The Polynomial Degree Closure construction uses the pd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L22-L26

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

theorem PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g + Q g) := by sorry
