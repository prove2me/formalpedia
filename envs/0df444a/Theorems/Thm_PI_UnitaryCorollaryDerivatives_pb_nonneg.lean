-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_nonneg
-- name    : PI.UnitaryCorollaryDerivatives.pb_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:12.120147+00:00
-- url     : https://prove2.me/theorems/20b52a8e-2a89-4c3a-9ffe-177904f7976b
-- title:
--   Unitary Corollary Derivatives: pb nonneg
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean#L29-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
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

theorem PI.UnitaryCorollaryDerivatives.pb_nonneg {e : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : List (Bool × B.Mat k r), (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n →
      ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e := by sorry
