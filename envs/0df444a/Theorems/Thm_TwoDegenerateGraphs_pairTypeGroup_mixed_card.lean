-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_mixed_card
-- name    : TwoDegenerateGraphs.pairTypeGroup_mixed_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/07b48608-4113-49ac-9aa6-8038d7949eed
-- title:
--   TwoDegenerateGraphs.pairTypeGroup_mixed_card
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.pairTypeGroup_mixed_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by sorry
