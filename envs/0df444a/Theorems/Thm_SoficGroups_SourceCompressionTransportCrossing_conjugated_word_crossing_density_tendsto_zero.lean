-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_conjugated_word_crossing_density_tendsto_zero
-- name    : SoficGroups.SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/229ff5a9-d65b-4f9d-85c0-b28000561de8
-- title:
--   SoficGroups.SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
    {G : Type*} [Group G] (A : SoficGroups.SoficApproximation G)
    (u g : G)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hword : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (u * g * u⁻¹))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action u * (A.model n).action g *
            ((A.model n).action u)⁻¹)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by sorry
