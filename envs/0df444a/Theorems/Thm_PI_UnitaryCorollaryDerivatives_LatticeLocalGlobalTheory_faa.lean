-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_LatticeLocalGlobalTheory_faa
-- name    : PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.faa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:43.634805+00:00
-- url     : https://prove2.me/theorems/2124cb74-72f0-460f-afbf-29b9585ef1c2
-- title:
--   Lattice Local Global Theory: faa
-- statement:
--   The Lattice Local Global Theory construction uses the faa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L58-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean#L58-L124

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate
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
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.faa (n : ℕ) (cost : B.Mat k r → ℕ) (ψ : B.Mat k r → ℂ) (hψ : ContDiff ℝ ∞ ψ) (K : Set ℂ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (H : ∀ w, Good k r n w → w ≠ [] → ∀ g ∈ GV k r, ψ g ∈ K → ‖Dw w ψ g‖ ≤ C₀ * gN g ^ cw cost w) :
    ∀ m : ℕ, ∀ χ : ℂ → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ w, Good k r n w → w.length ≤ m → ∀ g ∈ GV k r, ψ g ∈ K →
        ‖Dw w (fun g => χ (ψ g)) g‖ ≤ C * gN g ^ cw cost w := by sorry
