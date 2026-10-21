-- Prove2me | Theorems.Thm_RegMatroidXC_Main_proposition_18
-- name    : RegMatroidXC.Main.proposition_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:33.195915+00:00
-- url     : https://prove2.me/theorems/aa6be752-ba75-469e-bd2d-23ea1aeaa70e
-- title:
--   Proposition 18 — xc(P_{T}(M₀), Q_{T}(M₀)) = O(|V(G)|·|E(G)|) for a cographic centre M₀ = M*(G), Tᵢ = δ(vᵢ)
-- statement:
--   There is an absolute constant $c$ with the following property. Let $G$ be a connected finite graph (parallel edges and loops allowed) with vertex set $V(G)$ and edge set $E(G)$, let $V^* = \{v_1, \dots, v_k\}$ be a nonempty stable set of $G$ in which every $v_i$ has degree 3, let $T_i := \delta(v_i)$ be the set of the three edges at $v_i$, with named edges $T_i = \{\alpha_i, \beta_i, \gamma_i\}$, and let $M_0 := M^*(G)$ be the cographic matroid of $G$. Then some polytope $R$ with
--   $$P_{T_1,\dots,T_k}(M_0) \subseteq R \subseteq Q_{T_1,\dots,T_k}(M_0)$$
--   has an extended formulation with at most $c \cdot |V(G)| \cdot |E(G)|$ inequalities; that is,
--   $$\mathrm{xc}\big(P_{T_1,\dots,T_k}(M_0), Q_{T_1,\dots,T_k}(M_0)\big) = O(|V(G)| \cdot |E(G)|).$$
--
--   With Proposition 15 this gives Lemma 5 when the centre of the star decomposition is cographic.
--
--   **Formalization Note** The graph is given by a finite vertex type and, for every element $e$, an edge from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$; $M_0 = M^*(G)$ means that the dual $M_0^*$ is the cycle matroid of $G$. "Stable set of degree-3 nodes" is encoded as: the $v_i$ are distinct, no edge (including a loop) joins $v_i$ to $v_j$ for any $i, j$, and $\delta(v_i)$ consists of exactly the three edges $\alpha_i, \beta_i, \gamma_i$; with no loop at $v_i$ this is degree 3. The paper's polytope $R_{T_1,\dots,T_k}(M_0)$ ((14)–(17), pp. 11–12) is not formalized: the statement asserts the existence of a polytope between the pair with a formulation of the stated size, which is the stated consequence. The constant $c$ is chosen before the graph.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 12, Proposition 18

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
import Definitions.Def_RegMatroidXC_Main_Pairs
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem proposition_18 : ∃ c : ℝ, ∀ (α : Type) (M₀ : Matroid α) [Fintype M₀.E]
    (V : Type) [Fintype V] [DecidableEq V] (tail head : α → V),
    IsCycleMatroidOf M₀✶ V tail head → MultigraphConnected M₀ V tail head →
    ∀ (k : ℕ) (v : Fin k → V) (tri : Fin k → Fin 3 → α),
      1 ≤ k → Function.Injective v →
      (∀ i j, ∀ e ∈ M₀.E, ¬ (tail e = v i ∧ head e = v j)) →
      (∀ i, Function.Injective (tri i) ∧
        triSet tri i = {e | e ∈ M₀.E ∧ (tail e = v i ∨ head e = v i)}) →
      ∃ R : Set (PairIdx M₀ tri → ℝ), PolyP M₀ tri ⊆ R ∧ R ⊆ PolyQ M₀ tri ∧
        ∃ r : ℕ, IsEFOfSize R r ∧
          (r : ℝ) ≤ c * (Fintype.card V : ℝ) * (Fintype.card M₀.E : ℝ) := by sorry

end RegMatroidXC.Main
