-- Prove2me | Theorems.Thm_PI_QuotInvW_ineq
-- name    : PI.QuotInvW.ineq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:18:36.905816+00:00
-- url     : https://prove2.me/theorems/d5b4087d-54d3-44d8-8045-65abd0a3e368
-- title:
--   Quot Inv W: ineq
-- statement:
--   The Quot Inv W construction uses the ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L40-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableAvgS.lean#L40-L123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

theorem PI.QuotInvW.ineq (h : QuotientSetting G S μG μS ν) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x)
    {g : MtM m} (hg : Matrix.of g ∈ G) :
    ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := by sorry
