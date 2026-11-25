-- Prove2me | Theorems.Thm_PI_QuotInvW_ae_mem_G
-- name    : PI.QuotInvW.ae_mem_G
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:18:13.13174+00:00
-- url     : https://prove2.me/theorems/773a1f48-b0d5-5bec-9981-8adf29f9fb9f
-- title:
--   Quot Inv W: ae mem G
-- statement:
--   The Quot Inv W construction uses the ae mem G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L103-L105

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

theorem PI.QuotInvW.ae_mem_G (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by sorry
