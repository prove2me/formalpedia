-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_16
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:16.678645+00:00
-- url     : https://prove2.me/theorems/dee08964-3297-485e-bcca-2ba375d27df9
-- title:
--   Lemma 3.16 — balance-to-bipartiteness reduction
-- statement:
--   For every loopless signed colored graph whose three color classes are matchings, construct $G(F,b)$ using the explicit paths and the $7n$ vertices defined in the reduction layer. It is simple and has maximum degree at most three, and
--   $$G(F,b)\text{ is bipartite}\iff(F,b)\text{ is balanced},$$
--   $$\operatorname{del}_{\mathrm{BIP}}(G(F,b))=\operatorname{dist}_{\mathrm{BIP}}(G(F,b))=\operatorname{fr}(F,b).$$
--   There is a single finite constant $K$ such that every ordinary adjacency XOR query can be simulated by at most $K$ signed color-port XOR queries. The simulation is exact on every state of the logical query and answer registers, with input-independent gates and a clean embedding chosen before the signed graph. This supplies the operational reduction used by the goal theorem.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.16, PDF = printed page 20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_16 :
    (∀ n : ℕ, ∀ F : Finset (ColoredEdge n), Consistent F → ∀ b : ColoredEdge n → Bool,
      IsGraph (Gadget F b) ∧ DegreeBound 3 (Gadget F b) ∧
      (Bipartite (Gadget F b) ↔ Balanced F b) ∧
      DeletionDistance (Gadget F b) = Frustration F b ∧
      EditDistance (Gadget F b) = Frustration F b) ∧
    (∃ K : ℕ, CoherentSimulation K) := by sorry

end QuantumBipartiteTesting.Bipartiteness
