-- Prove2me | Theorems.Thm_PIW_HCFdeg_toL2Map_apply
-- name    : PIW.HCFdeg.toL2Map_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:20.990808+00:00
-- url     : https://prove2.me/theorems/6be978fa-6503-437b-b81c-9a69bd6c3c23
-- title:
--   HCFdeg: to L2 Map apply
-- statement:
--   The HCFdeg construction uses the to L2 Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L28-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory Filter Topology
variable {X H : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

theorem PIW.HCFdeg.toL2Map_apply (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) (v : H) :
    toL2Map c hL v = (hL v).toLp (c v) := by sorry
