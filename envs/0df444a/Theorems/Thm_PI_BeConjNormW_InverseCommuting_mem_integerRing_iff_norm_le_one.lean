-- Prove2me | Theorems.Thm_PI_BeConjNormW_InverseCommuting_mem_integerRing_iff_norm_le_one
-- name    : PI.BeConjNormW.InverseCommuting.mem_integerRing_iff_norm_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:06.50941+00:00
-- url     : https://prove2.me/theorems/a20fa392-328d-44eb-b36b-648353a00e6b
-- title:
--   Inverse Commuting: mem integer Ring iff norm le one
-- statement:
--   The Inverse Commuting construction uses the mem integer Ring iff norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/MemIntegerRingIffNormLeOne.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/MemIntegerRingIffNormLeOne.lean#L14-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical PowerSeries
open PI PI.BeConjNormW
open PI.BeConjNormW.InverseCommuting
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeConjNormW.InverseCommuting.mem_integerRing_iff_norm_le_one (x : ℂ_[p]) : x ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p ↔ ‖x‖ ≤ 1 := by sorry
