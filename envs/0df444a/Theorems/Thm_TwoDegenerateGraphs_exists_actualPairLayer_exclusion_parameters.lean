-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_exists_actualPairLayer_exclusion_parameters
-- name    : TwoDegenerateGraphs.exists_actualPairLayer_exclusion_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/37a58c6c-fb71-43de-a863-9a6ad3851573
-- title:
--   TwoDegenerateGraphs.exists_actualPairLayer_exclusion_parameters
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.exists_actualPairLayer_exclusion_parameters :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ layer : Fin depth,
        let layerSize :=
          Fintype.card (PairLayer baseSize layer.val)
        4 ≤ layerSize ∧
        empiricalEntropyError layerSize < entropySlack ∧
        (layerSize : ℝ) +
          3 * logTwo ((layerSize.choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * (layerSize.choose 2 : ℝ) < -1 := by sorry
