-- Prove2me | Theorems.Thm_RegMatroidXC_Main_proposition_16
-- name    : RegMatroidXC.Main.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:41.481952+00:00
-- url     : https://prove2.me/theorems/843e94b5-ff0c-4ab3-a2f6-afd4787858aa
-- title:
--   Proposition 16 — xc(P_{T}(M₀), Q_{T}(M₀)) = O(|V(G)|·|E(G)|) for a graphic centre M₀ = M(G)
-- statement:
--   There is an absolute constant $c$ with the following property. Let $G$ be a connected finite graph (parallel edges and loops allowed) with vertex set $V(G)$ and edge set $E(G)$, let $M_0 := M(G)$ be its graphic matroid, and let $T_1, \dots, T_k$ be pairwise edge-disjoint triangles of $G$ with named edges $T_i = \{\alpha_i, \beta_i, \gamma_i\}$. Then some polytope $R$ with
--   $$P_{T_1,\dots,T_k}(M_0) \subseteq R \subseteq Q_{T_1,\dots,T_k}(M_0)$$
--   has an extended formulation with at most $c \cdot |V(G)| \cdot |E(G)|$ inequalities; that is,
--   $$\mathrm{xc}\big(P_{T_1,\dots,T_k}(M_0), Q_{T_1,\dots,T_k}(M_0)\big) = O(|V(G)| \cdot |E(G)|).$$
--
--   With Proposition 15 this gives Lemma 5 when the centre of the star decomposition is graphic.
--
--   **Formalization Note** The graph is given by a finite vertex type and, for every element $e$, an edge from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$; $M_0 = M(G)$ is expressed through the oriented incidence matrix. A triangle of $G$ is a 3-element circuit of $M(G)$ (three edges forming a cycle of length 3). The paper's polytope $R_{T_1,\dots,T_k}(M_0)$, defined by (7)–(13), is not formalized: the statement asserts the existence of a polytope between the pair with a formulation of the stated size, which is the stated consequence. The constant $c$ is chosen before the graph.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 10, Proposition 16

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Pairs
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem proposition_16 : ∃ c : ℝ, ∀ (α : Type) (M₀ : Matroid α) [Fintype M₀.E]
    (V : Type) [Fintype V] [DecidableEq V] (tail head : α → V),
    IsCycleMatroidOf M₀ V tail head → MultigraphConnected M₀ V tail head →
    ∀ (k : ℕ) (tri : Fin k → Fin 3 → α),
      (∀ i, Function.Injective (tri i) ∧ M₀.IsCircuit (triSet tri i)) →
      Pairwise (fun i j => Disjoint (triSet tri i) (triSet tri j)) →
      ∃ R : Set (PairIdx M₀ tri → ℝ), PolyP M₀ tri ⊆ R ∧ R ⊆ PolyQ M₀ tri ∧
        ∃ r : ℕ, IsEFOfSize R r ∧
          (r : ℝ) ≤ c * (Fintype.card V : ℝ) * (Fintype.card M₀.E : ℝ) := by sorry

end RegMatroidXC.Main
