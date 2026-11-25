-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_det_star
-- name    : PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_det_star
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:45.176029+00:00
-- url     : https://prove2.me/theorems/2eb97577-733e-457e-bc91-fc8fc67e77d1
-- title:
--   Polynomial Degree Closure: pd det star
-- statement:
--   The Polynomial Degree Closure construction uses the pd det star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L86-L92

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

theorem PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_det_star (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => star (M g i j))) : IsPolyDeg n (fun g => star (M g).det) := by sorry
