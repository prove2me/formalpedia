-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_Dw_clm
-- name    : PI.UnitaryCorollaryDerivatives.pb_Dw_clm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:06.875736+00:00
-- url     : https://prove2.me/theorems/cd66da33-e3b7-47c5-aa24-0e623696317f
-- title:
--   Unitary Corollary Derivatives: pb Dw clm
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb Dw clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L62-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L62-L91

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
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
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.pb_Dw_clm {K : ℝ} (hK : 0 ≤ K) (w : List (Bool × B.Mat k r))
    (hw : ∀ x ∈ w, ∀ g, ‖dirL x g‖ ≤ K * ‖g‖) :
    ∀ (Λ : B.Mat k r →L[ℝ] ℂ) (c : ℝ), 0 ≤ c → (∀ g, ‖Λ g‖ ≤ c * ‖g‖) → ∃ Λ' : B.Mat k r →L[ℝ] ℂ,
      Dw w (fun g => Λ g) = (fun g => Λ' g) ∧ ∀ g, ‖Λ' g‖ ≤ c * K ^ w.length * ‖g‖ := by sorry
