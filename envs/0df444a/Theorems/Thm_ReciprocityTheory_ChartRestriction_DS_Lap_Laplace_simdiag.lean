-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_simdiag
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.simdiag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:23.016066+00:00
-- url     : https://prove2.me/theorems/faf3e93b-4c53-5119-aa49-50946736e915
-- title:
--   Laplace: simdiag
-- statement:
--   The Laplace construction uses the simdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L23-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L23-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
open scoped MatrixOrder

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.simdiag {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, IsUnit P ∧ ∃ c : Fin d → ℝ,
      Pᵀ * A * P = 1 ∧ Pᵀ * C * P = diagonal c := by sorry
