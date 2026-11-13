-- Prove2me | Theorems.Thm_Thm11SourceRoute_partitionOscillation_le_good_bad_split
-- name    : Thm11SourceRoute.partitionOscillation_le_good_bad_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:45:09.51006+00:00
-- url     : https://prove2.me/theorems/18d073c1-8d69-4925-aa2c-57300c4c3fbf
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.partitionOscillation_le_good_bad_split
-- statement:
--   Source theorem `Thm11SourceRoute.partitionOscillation_le_good_bad_split` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F007
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem partitionOscillation_le_good_bad_split
    {f α : ℝ → ℝ} {a b C eta : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (B : Finset ℕ)
    (heta_nonneg : 0 ≤ eta)
    (hgood :
      ∀ i : Fin P.n, i.val ∉ B →
        upperStep P f i - lowerStep P f i ≤ eta)
    (hbad :
      ∀ i : Fin P.n, i.val ∈ B →
        upperStep P f i - lowerStep P f i ≤ 2 * C) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
            (α (P.pts i.succ) - α (P.pts i.castSucc))) := by sorry

end Thm11SourceRoute
