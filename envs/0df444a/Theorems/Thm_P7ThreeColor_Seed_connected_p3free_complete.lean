-- Prove2me | Theorems.Thm_P7ThreeColor_Seed_connected_p3free_complete
-- name    : P7ThreeColor.Seed.connected_p3free_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:45.975061+00:00
-- url     : https://prove2.me/theorems/8a3e9c2b-313a-4bed-a861-fcf4c6e27983
-- title:
--   Proof of Corollary 5, p. 6 — a connected P₃-free graph is complete
-- statement:
--   Let $H$ be a connected simple graph with no induced path on three vertices. Every two distinct vertices of $H$ are adjacent:
--
--   $$
--   u\ne v\quad\Longrightarrow\quad uv\in E(H).
--   $$
--
--   This is the completeness observation used in the final case of Corollary 5.
--
--   **Formalization Note** No finiteness assumption is required for this observation. Connectedness includes a nonempty vertex set.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, proof of Corollary 5, final sentence

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Seed

/-- Proof of Corollary 5, p. 6: a connected `P₃`-free graph is complete. -/
theorem connected_p3free_complete {W : Type*} (H : SimpleGraph W)
    (hH : H.Connected) (h3 : PFree 3 H) :
    ∀ u v : W, u ≠ v → H.Adj u v := by sorry

end P7ThreeColor.Seed
