-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_3
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:12:55.83356+00:00
-- url     : https://prove2.me/theorems/c6a1cea4-71f7-44ed-9885-07551d6dacff
-- title:
--   Lemma 3.3 — random-sign frustration bound
-- statement:
--   Let $F$ be any finite colored multigraph on $N$ vertices, with $m$ distinct colored edges, and assign independent uniform signs to those edges. For every $0<\tau<1/2$,
--   $$\Pr[\operatorname{fr}(F,b)\le\tau m]\le2^{N-(1-h_2(\tau))m},$$
--   where $h_2$ is binary entropy in base two. There is a positive absolute constant $c$ such that, for every such graph with $m\ge1.3N$,
--   $$\Pr[\operatorname{fr}(F,b)\le m/50]\le2^{-cN}.$$
--   The constants are independent of the graph and its color count. This is the farness estimate for random signed constraints.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.3, PDF = printed page 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_3 :
    (∀ N colors : ℕ, ∀ F : Finset (ColoredEdge N colors), Consistent F →
      ∀ τ : ℝ, 0 < τ → τ < 1/2 →
        FrustrationTail F (τ * F.card) ≤
          (2 : ℝ) ^ ((N : ℝ) - (1 - BinaryEntropy τ) * F.card)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ N colors : ℕ, ∀ F : Finset (ColoredEdge N colors),
      Consistent F → (13/10 : ℝ) * N ≤ F.card →
        FrustrationTail F ((F.card : ℝ)/50) ≤ (2 : ℝ) ^ (-c*N)) := by sorry

end QuantumBipartiteTesting.Bipartiteness
