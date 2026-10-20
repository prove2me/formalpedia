-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_free_of_layer_exclusion
-- name    : TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/37a631f1-2bc1-419e-b480-16812a298bf6
-- title:
--   TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by sorry
