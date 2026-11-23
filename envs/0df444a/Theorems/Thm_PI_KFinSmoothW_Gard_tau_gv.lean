-- Prove2me | Theorems.Thm_PI_KFinSmoothW_Gard_tau_gv
-- name    : PI.KFinSmoothW.Gard.tau_gv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:00.332552+00:00
-- url     : https://prove2.me/theorems/96b1183c-a208-4a5f-9b32-3c4850b2fa06
-- title:
--   Gard: tau gv
-- statement:
--   The Gard construction uses the tau gv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/Garding.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/Garding.lean#L92-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem PI.KFinSmoothW.Gard.tau_gv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x : H)
    (γ : UJ ε) :
    τ (umat γ) (gv ε τ Φ x) =
      ∫ h, Φ (Jm ε * (umat γ)ᴴ * Jm ε * umat h) • τ (umat h) x ∂(muG ε) := by sorry
