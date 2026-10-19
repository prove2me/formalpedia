-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_parent_child_hammingDist_le
-- name    : TwoDegenerateGraphs.pairGraphCopy_parent_child_hammingDist_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/b1b17927-7a34-4325-a3dd-37e59df442b6
-- title:
--   TwoDegenerateGraphs.pairGraphCopy_parent_child_hammingDist_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopy_parent_child_hammingDist_le
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (pair :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist
      (pairGraphCopyParentWords retained copy layer parent)
      (pairGraphCopyChildWords retained copy layer pair) ≤ radius := by sorry
