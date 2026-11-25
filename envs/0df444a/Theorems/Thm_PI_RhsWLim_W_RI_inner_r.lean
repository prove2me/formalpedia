-- Prove2me | Theorems.Thm_PI_RhsWLim_W_RI_inner_r
-- name    : PI.RhsWLim.W.RI.inner_r
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:21.154352+00:00
-- url     : https://prove2.me/theorems/a7302db5-921b-5241-8fef-a6b3f9e8c800
-- title:
--   RI: inner r
-- statement:
--   The RI construction uses the inner r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvR.lean#L32-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvR.lean#L32-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem PI.RhsWLim.W.RI.inner_r (hW : IsHaarOn (UWset k r z') μW') (M : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ)
    (b : Mat k r) (hb : b ∈ UWset k r z') :
    ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW' =
      ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by sorry
