-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_averageDisagreement_le_tau
-- name    : TwoDegenerateGraphs.pairGraphCopy_averageDisagreement_le_tau
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/459801e5-7613-4b3a-9e9b-b24b6d3b8c87
-- title:
--   TwoDegenerateGraphs.pairGraphCopy_averageDisagreement_le_tau
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopy_averageDisagreement_le_tau
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤ tau := by sorry
