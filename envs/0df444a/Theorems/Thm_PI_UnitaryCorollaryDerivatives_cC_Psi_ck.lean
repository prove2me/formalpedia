-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_Psi_ck
-- name    : PI.UnitaryCorollaryDerivatives.cC_Psi_ck
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:15.867354+00:00
-- url     : https://prove2.me/theorems/d970f06d-5639-452e-840e-0b45e9196b3d
-- title:
--   Unitary Corollary Derivatives: c C Psi ck
-- statement:
--   The Unitary Corollary Derivatives construction uses the c C Psi ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CCCNonneg.lean#L32-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CCCNonneg.lean#L32-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
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
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cC_Psi_ck {r : ℕ} {Q mm : ℕ} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn (mm : ℕ∞) (B.GV k r) f) {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    (hQ : Q + w.length ≤ mm) : B.CkOn (Q : ℕ∞) (B.GV k r) (B.Rw w (fun g => φ g • f g)) := by sorry
