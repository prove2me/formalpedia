-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_sum_cost_le
-- name    : PI.UnitaryCorollaryDerivatives.sum_cost_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:02:02.616124+00:00
-- url     : https://prove2.me/theorems/4c4af852-91b8-47ee-b3d4-7cf3a8c14b4e
-- title:
--   Unitary Corollary Derivatives: sum cost le
-- statement:
--   The Unitary Corollary Derivatives construction uses the sum cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L45-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
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

theorem PI.UnitaryCorollaryDerivatives.sum_cost_le {k r : ℕ} (c : B.Mat k r → ℕ) {u v u₁ v₁ : List (B.Mat k r)} (hu : u₁.Sublist u)
    (hv : v₁.Sublist v) : (((u₁ ++ v₁).map c).sum : ℝ) ≤ (((u ++ v).map c).sum : ℝ) := by sorry
