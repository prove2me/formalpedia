-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_ckOn_of_contDiff
-- name    : PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:09.897845+00:00
-- url     : https://prove2.me/theorems/0c0c2462-0686-4cc4-8e47-1248348c93a9
-- title:
--   Unitary Corollary Derivatives: ck On of cont Diff
-- statement:
--   The Unitary Corollary Derivatives construction uses the ck On of cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/WeightBoundMultiplicative.lean#L39-L43

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

theorem PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) : B.CkOn m (B.GV k r) f := by sorry
