-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairChildArrayAverageDisagreement_le_radius
-- name    : TwoDegenerateGraphs.pairChildArrayAverageDisagreement_le_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/42e7d399-a199-471c-bfc9-3999bc82a36b
-- title:
--   TwoDegenerateGraphs.pairChildArrayAverageDisagreement_le_radius
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.pairChildArrayAverageDisagreement_le_radius
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by sorry
