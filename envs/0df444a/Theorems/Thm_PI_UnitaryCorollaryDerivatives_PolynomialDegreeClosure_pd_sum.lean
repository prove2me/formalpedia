-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_sum
-- name    : PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:17:38.812051+00:00
-- url     : https://prove2.me/theorems/f0ccf897-90b3-43e0-bbd9-ca26f6620cbe
-- title:
--   Polynomial Degree Closure: pd sum
-- statement:
--   The Polynomial Degree Closure construction uses the pd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/GfPolyA.lean#L50-L59

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

theorem PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg a (P i)) : IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by sorry
