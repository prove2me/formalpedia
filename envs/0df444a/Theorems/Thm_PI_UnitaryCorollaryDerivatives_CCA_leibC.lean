-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_leibC
-- name    : PI.UnitaryCorollaryDerivatives.CCA.leibC
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:10.485176+00:00
-- url     : https://prove2.me/theorems/6bc174cc-c2d1-4564-9df4-0188d8e66ebe
-- title:
--   CCA: leib C
-- statement:
--   The CCA construction uses the leib C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L91-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompCA.lean#L91-L123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CCA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.CCA.leibC (g : Mat k r) (w : List (Bool × Mat k r)) :
    ∀ (a b : Mat k r → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ∀ M : ℝ,
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → (w₁ ++ w₂).Perm w →
        ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by sorry
