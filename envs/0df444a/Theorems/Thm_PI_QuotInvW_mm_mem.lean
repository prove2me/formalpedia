-- Prove2me | Theorems.Thm_PI_QuotInvW_mm_mem
-- name    : PI.QuotInvW.mm_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:10.042419+00:00
-- url     : https://prove2.me/theorems/103f8d14-463a-410f-9927-bc6d7cfc5839
-- title:
--   Quot Inv W: mm mem
-- statement:
--   The Quot Inv W construction uses the mm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L53-L55

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

theorem PI.QuotInvW.mm_mem {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a b : MtM m}
    (ha : Matrix.of a ∈ G) (hb : Matrix.of b ∈ G) : Matrix.of (mm a b) ∈ G := by sorry
