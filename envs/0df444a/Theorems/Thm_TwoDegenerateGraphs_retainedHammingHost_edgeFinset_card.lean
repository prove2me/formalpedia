-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_retainedHammingHost_edgeFinset_card
-- name    : TwoDegenerateGraphs.retainedHammingHost_edgeFinset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/55093e51-5806-450e-a022-80154319b7e4
-- title:
--   TwoDegenerateGraphs.retainedHammingHost_edgeFinset_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical

theorem TwoDegenerateGraphs.retainedHammingHost_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    (retainedHammingHost dimension radius retained).edgeFinset.card =
      (retainedHammingWordEdges dimension radius retained).card := by sorry
