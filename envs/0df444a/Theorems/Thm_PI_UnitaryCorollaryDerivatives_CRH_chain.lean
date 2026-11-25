-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_chain
-- name    : PI.UnitaryCorollaryDerivatives.CRH.chain
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:43:01.740111+00:00
-- url     : https://prove2.me/theorems/1c38a684-6529-51f7-9521-96ea1a6dfcea
-- title:
--   CRH: chain
-- statement:
--   The CRH construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L50-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L50-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.CRH.chain (x : Bool × Mat k r) {ψ : Mat k r → ℝ} {h : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h)
    (q : ℕ) :
    Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) =
      fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ) * Dx x (fun g => ((ψ g : ℝ) : ℂ)) g := by sorry
