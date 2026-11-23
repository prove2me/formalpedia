-- Prove2me | Theorems.Thm_PIW_HCFdeg_toL2Map_apply_ae_eq
-- name    : PIW.HCFdeg.toL2Map_apply_ae_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:25.027581+00:00
-- url     : https://prove2.me/theorems/ac130437-95d0-4025-82bc-50eae442ff28
-- title:
--   HCFdeg: to L2 Map apply ae eq
-- statement:
--   The HCFdeg construction uses the to L2 Map apply ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L31-L34

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

theorem PIW.HCFdeg.toL2Map_apply_ae_eq (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) (v : H) :
    (toL2Map c hL v : X → ℂ) =ᵐ[μ] c v := by sorry
