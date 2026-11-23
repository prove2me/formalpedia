-- Prove2me | Theorems.Thm_PI_QuotInvW_weil_inv
-- name    : PI.QuotInvW.weil_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:18.78289+00:00
-- url     : https://prove2.me/theorems/cd35d9b7-5039-4f73-97e3-563dd6f91628
-- title:
--   Quot Inv W: weil inv
-- statement:
--   The Quot Inv W construction uses the weil inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L107-L118

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

theorem PI.QuotInvW.weil_inv (h : QuotientSetting G S μG μS ν) {H f : MtM m → ℝ≥0∞} (hH : Measurable H)
    (hf : Measurable f) (hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → H (mm s x) = H x) :
    ∫⁻ x, H x * f x ∂μG = ∫⁻ x, H x * (∫⁻ s, f (mm s x) ∂μS) ∂ν := by sorry
