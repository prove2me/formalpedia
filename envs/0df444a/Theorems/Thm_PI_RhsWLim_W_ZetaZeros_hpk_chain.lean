-- Prove2me | Theorems.Thm_PI_RhsWLim_W_ZetaZeros_hpk_chain
-- name    : PI.RhsWLim.W.ZetaZeros.hpk_chain
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:40.478076+00:00
-- url     : https://prove2.me/theorems/403d4726-3683-44cf-b13d-1c413cbaa8a8
-- title:
--   Zeta Zeros: hpk chain
-- statement:
--   The Zeta Zeros construction uses the hpk chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsHaar.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsHaar.lean#L143-L146

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
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
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem PI.RhsWLim.W.ZetaZeros.hpk_chain (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    Hpk k r *ᵥ (embWb k r μ *ᵥ (MB.Em k r *ᵥ u)) = MB.Em k r *ᵥ (Hb k *ᵥ (μ *ᵥ u)) := by sorry
