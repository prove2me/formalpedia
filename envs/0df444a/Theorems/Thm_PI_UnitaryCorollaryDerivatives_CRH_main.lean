-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_main
-- name    : PI.UnitaryCorollaryDerivatives.CRH.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:30:43.163899+00:00
-- url     : https://prove2.me/theorems/9e0e35f1-27f9-40f2-8e64-1aca6ac57c85
-- title:
--   CRH: main
-- statement:
--   The CRH construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L80-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L80-L137

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

theorem PI.UnitaryCorollaryDerivatives.CRH.main (ψ : Mat k r → ℝ) (h : ℝ → ℝ) (cost : Mat k r → ℕ) (n : ℕ) (C₀ : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * gN g ^ cs cost w) :
    ∀ m q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g‖ ≤ K * gN g ^ cs cost w := by sorry
