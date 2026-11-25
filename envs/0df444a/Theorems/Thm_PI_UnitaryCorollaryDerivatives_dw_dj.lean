-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_dw_dj
-- name    : PI.UnitaryCorollaryDerivatives.dw_dj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:06.660876+00:00
-- url     : https://prove2.me/theorems/0fad0159-e413-4f7e-a2bb-06131660aaf3
-- title:
--   Unitary Corollary Derivatives: dw dj
-- statement:
--   The Unitary Corollary Derivatives construction uses the dw dj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/MxLeOne.lean#L25-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/MxLeOne.lean#L25-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_MxLeOne
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem PI.UnitaryCorollaryDerivatives.dw_dj (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by sorry
