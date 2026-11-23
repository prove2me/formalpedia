-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_sum
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.IsPD.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:29.326502+00:00
-- url     : https://prove2.me/theorems/9105f7a8-9bd8-44e3-b476-7e52f536cce7
-- title:
--   Is PD: sum
-- statement:
--   The Is PD construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean#L70-L72

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix

theorem PI.UnitaryGroupMassFormula.PolyCoef.IsPD.sum {N : ℕ} {ι : Type*} (s : Finset ι) {F : ι → UG N → ℂ} (hF : ∀ i ∈ s, IsPD (F i)) :
    IsPD (fun g => ∑ i ∈ s, F i g) := by sorry
