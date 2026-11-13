-- Prove2me | Theorems.Thm_Thm11SourceRoute_partitionOscillation_le_goodRemainder_badIntervals
-- name    : Thm11SourceRoute.partitionOscillation_le_goodRemainder_badIntervals
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:08:45.580792+00:00
-- url     : https://prove2.me/theorems/542cddfd-9630-48c6-a40b-be80456ca14b
-- title:
--   Chapter 1, thm_1_1_bad_cells: Thm11SourceRoute.partitionOscillation_le_goodRemainder_badIntervals
-- statement:
--   Source theorem `Thm11SourceRoute.partitionOscillation_le_goodRemainder_badIntervals` from Chapter 1, module `thm_1_1_bad_cells`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_bad_cells.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_bad_cells_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F000
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

theorem partitionOscillation_le_goodRemainder_badIntervals
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (hα_mono : Monotone α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (hC_nonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆
          goodRemainder a b S (fun c : ℝ => rho c / 2) →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh_bad : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C * ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by sorry

end Thm11SourceRoute
