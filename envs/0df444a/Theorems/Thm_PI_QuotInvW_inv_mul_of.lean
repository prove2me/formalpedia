-- Prove2me | Theorems.Thm_PI_QuotInvW_inv_mul_of
-- name    : PI.QuotInvW.inv_mul_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:15.720225+00:00
-- url     : https://prove2.me/theorems/ca9c3cd6-b574-437a-b392-0523c3d54077
-- title:
--   Quot Inv W: inv mul of
-- statement:
--   The Quot Inv W construction uses the inv mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean#L44-L46

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

theorem PI.QuotInvW.inv_mul_of {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ G) : a⁻¹ * a = 1 := by sorry
