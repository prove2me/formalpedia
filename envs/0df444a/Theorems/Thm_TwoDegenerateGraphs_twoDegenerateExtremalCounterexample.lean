-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_twoDegenerateExtremalCounterexample
-- name    : TwoDegenerateGraphs.twoDegenerateExtremalCounterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:43.893326+00:00
-- url     : https://prove2.me/theorems/24f47bda-4f5b-41ab-ad9a-b384ac3d7d10
-- title:
--   TwoDegenerateGraphs.twoDegenerateExtremalCounterexample
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

theorem TwoDegenerateGraphs.twoDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by sorry
