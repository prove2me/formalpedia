-- Prove2me | Theorems.Thm_PI_QuotInvW_weil
-- name    : PI.QuotInvW.weil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:37.673311+00:00
-- url     : https://prove2.me/theorems/c787df4b-4092-402d-b06a-c6eabcb1fdd2
-- title:
--   Quot Inv W: weil
-- statement:
--   The Quot Inv W construction uses the weil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L66-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

theorem PI.QuotInvW.weil (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν := by sorry
