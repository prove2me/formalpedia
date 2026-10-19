-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingHost_adj_iff
-- name    : TwoDegenerateGraphs.hammingHost_adj_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/053a566c-d752-4298-8f3b-4488361c24ea
-- title:
--   TwoDegenerateGraphs.hammingHost_adj_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingHost_adj_iff (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by sorry
