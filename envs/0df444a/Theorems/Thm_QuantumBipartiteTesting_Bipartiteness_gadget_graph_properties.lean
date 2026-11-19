-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_gadget_graph_properties
-- name    : QuantumBipartiteTesting.Bipartiteness.gadget_graph_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:20:05.129999+00:00
-- url     : https://prove2.me/theorems/a73a0bbc-e0a0-41b3-8325-dd6221cf2e39
-- title:
--   Seven-vertex path gadget preserves frustration and bipartiteness
-- statement:
--   Let $F$ be a signed colored multigraph on $n$ vertices with three colors, with no loops and at most one incident edge of each color at any vertex. Let $b$ assign a Boolean sign to every colored edge. Construct $G(F,b)$ on exactly $7n$ vertices by replacing a sign-zero edge by an even path of length two, and a sign-one edge by an odd path of length three. The two auxiliary vertices reserved for each vertex and color are used only by the corresponding oriented edge; unused auxiliaries are isolated.
--
--   Then $G(F,b)$ is a simple graph of maximum degree three, and
--
--   $$
--   G(F,b)\text{ is bipartite}\quad\Longleftrightarrow\quad (F,b)\text{ is balanced}.
--   $$
--
--   Moreover, both the minimum number of edge deletions and the minimum number of edge additions and deletions required to make $G(F,b)$ bipartite equal the frustration of the signed instance:
--
--   $$
--   \operatorname{del}_{\mathrm{bip}}(G(F,b))
--   =\operatorname{edit}_{\mathrm{bip}}(G(F,b))
--   =\operatorname{fr}(F,b).
--   $$
--
--   This is the graph-theoretic component of Lemma 3.16. It transfers signed constraint distance to ordinary graph distance; the coherent oracle simulation is a separate component.
-- source:
--   Kayal, Sen, Szabó, held October 2026 manuscript, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §3.6 pp.20–21, Lemma 3.16, equations (29)–(30) and following edge-modification paragraph.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

theorem QuantumBipartiteTesting.Bipartiteness.gadget_graph_properties (n : ℕ)
    (F : Finset (QuantumBipartiteTesting.Bipartiteness.ColoredEdge n))
    (hF : QuantumBipartiteTesting.Bipartiteness.Consistent F)
    (b : QuantumBipartiteTesting.Bipartiteness.ColoredEdge n → Bool) :
    QuantumBipartiteTesting.Bipartiteness.IsGraph (QuantumBipartiteTesting.Bipartiteness.Gadget F b) ∧
    QuantumBipartiteTesting.Bipartiteness.DegreeBound 3 (QuantumBipartiteTesting.Bipartiteness.Gadget F b) ∧
    (QuantumBipartiteTesting.Bipartiteness.Bipartite (QuantumBipartiteTesting.Bipartiteness.Gadget F b) ↔
      QuantumBipartiteTesting.Bipartiteness.Balanced F b) ∧
    QuantumBipartiteTesting.Bipartiteness.DeletionDistance (QuantumBipartiteTesting.Bipartiteness.Gadget F b) =
      QuantumBipartiteTesting.Bipartiteness.Frustration F b ∧
    QuantumBipartiteTesting.Bipartiteness.EditDistance (QuantumBipartiteTesting.Bipartiteness.Gadget F b) =
      QuantumBipartiteTesting.Bipartiteness.Frustration F b := by sorry
