-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopyChildWords_retained
-- name    : TwoDegenerateGraphs.pairGraphCopyChildWords_retained
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/742af5b6-5e53-407a-9c79-c0a9cc122109
-- title:
--   TwoDegenerateGraphs.pairGraphCopyChildWords_retained
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopyChildWords_retained
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) :
    retained ∈
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference)
        (pairGraphCopyChildWords retained copy layer) := by sorry
