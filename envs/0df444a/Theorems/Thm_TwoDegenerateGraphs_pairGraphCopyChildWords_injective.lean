-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphCopyChildWords_injective
-- name    : TwoDegenerateGraphs.pairGraphCopyChildWords_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/b4298df4-e979-43f9-8d64-21fc32da7c3f
-- title:
--   TwoDegenerateGraphs.pairGraphCopyChildWords_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.pairGraphCopyChildWords_injective
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained copy layer) := by sorry
