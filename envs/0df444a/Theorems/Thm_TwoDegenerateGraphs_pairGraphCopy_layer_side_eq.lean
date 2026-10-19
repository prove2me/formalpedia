-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_layer_side_eq
-- name    : TwoDegenerateGraphs.pairGraphCopy_layer_side_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/2f382ca5-0db8-4e3b-b9a1-c7d9f21386a1
-- title:
--   TwoDegenerateGraphs.pairGraphCopy_layer_side_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopy_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize layer) :
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by sorry
