-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_layer_entropy_upper_of_disagreement
-- name    : TwoDegenerateGraphs.pairGraphCopy_layer_entropy_upper_of_disagreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/4c9bcae2-ed90-4bdd-909d-da2714386901
-- title:
--   TwoDegenerateGraphs.pairGraphCopy_layer_entropy_upper_of_disagreement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopy_layer_entropy_upper_of_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        entropyLowerEndpoint +
          (pairGraphCopyLayerPotential retained copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by sorry
