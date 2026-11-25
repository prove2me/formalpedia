-- Prove2me | Theorems.Thm_PIW_HCFdeg_continuous_toL2Map
-- name    : PIW.HCFdeg.continuous_toL2Map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:38.686562+00:00
-- url     : https://prove2.me/theorems/15126646-932e-5b4d-a024-24cd98f4d4cc
-- title:
--   HCFdeg: continuous to L2 Map
-- statement:
--   The HCFdeg construction uses the continuous to L2 Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean#L36-L50

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

theorem PIW.HCFdeg.continuous_toL2Map [CompleteSpace H] (c : H →ₗ[ℂ] (X → ℂ))
    (hcont : ∀ x, Continuous fun v => c v x) (hL : ∀ v, MemLp (c v) 2 μ) :
    Continuous (toL2Map c hL) := by sorry
