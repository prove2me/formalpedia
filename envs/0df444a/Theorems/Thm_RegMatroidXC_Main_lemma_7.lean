-- Prove2me | Theorems.Thm_RegMatroidXC_Main_lemma_7
-- name    : RegMatroidXC.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:39.2406+00:00
-- url     : https://prove2.me/theorems/cae5a630-82f0-432c-b3c7-f907128114c2
-- title:
--   Lemma 7 — every node-weighted tree has a node v₀ whose removal leaves components of weight ≤ W/2
-- statement:
--   Let $T$ be a finite tree with node weights $w : V(T) \to \mathbb R$ and total weight $W = \sum_{v} w(v)$. Then there is a node $v_0$ such that every connected component $K$ of $T - v_0$ satisfies
--   $$\sum_{v \in K} w(v) \le \frac W2 .$$
--
--   In the proof of Lemma 4 this node is the centre of the star decomposition.
--
--   **Formalization Note** The weights are arbitrary reals (the paper's proof does not use nonnegativity). For a one-node tree, $T - v_0$ has no components and the statement holds trivially.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 3, Lemma 7

import Mathlib

namespace RegMatroidXC.Main

open Classical in
theorem lemma_7 {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (w : V → ℝ) :
    ∃ v₀ : V, ∀ c : (T.induce ({v₀}ᶜ : Set V)).ConnectedComponent,
      (∑ v : ({v₀}ᶜ : Set V),
          if (T.induce ({v₀}ᶜ : Set V)).connectedComponentMk v = c then w v else 0)
        ≤ (∑ v, w v) / 2 := by sorry

end RegMatroidXC.Main
