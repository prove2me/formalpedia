-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TangleTree_result_10_3
-- name    : RobertsonSeymour1991.GM10.TangleTree.result_10_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:21.948497+00:00
-- url     : https://prove2.me/theorems/63d637fa-2d9e-494c-89d8-37635131bb2a
-- title:
--   (10.3), p. 181 — mutually distinguishable tangles have a tree-decomposition separating them by their distinctions
-- statement:
--   Let $\mathcal T_1,\dots,\mathcal T_n$ ($n\ge 1$) be mutually distinguishable tangles in a finite hypergraph $G$, of orders $\theta_1,\dots,\theta_n$ (for $i\neq j$, $\mathcal T_i\not\subseteq\mathcal T_j$), and let $\lambda$ be a tie-breaker in $G$. Then there is a tree-decomposition $(T,\tau)$ of $G$ with $V(T)=\{t_1,\dots,t_n\}$ (the $t_i$ distinct) such that:
--
--   1. for every edge $e\in E(T)$ and every $i$, if $T_1,T_2$ are the components of $T\setminus e$ and $t_i\in V(T_1)$, then
--   $$\Bigl(\bigcup_{t\in V(T_1)}\tau(t),\ \bigcup_{t\in V(T_2)}\tau(t)\Bigr)\notin\mathcal T_i;$$
--   2. for all $i\neq j$, if $e$ is an edge of the path of $T$ between $t_i$ and $t_j$ making separations of smallest $\lambda$-order among the edges of that path, then the separations made by $e$ are the $(\mathcal T_i,\mathcal T_j)$- and $(\mathcal T_j,\mathcal T_i)$-distinctions. Precisely, if $T_1$ is the component of $T\setminus e$ containing $t_i$ and $T_2$ the one containing $t_j$, then $\bigl(\bigcup_{V(T_2)}\tau,\ \bigcup_{V(T_1)}\tau\bigr)$ is the $(\mathcal T_i,\mathcal T_j)$-distinction and $\bigl(\bigcup_{V(T_1)}\tau,\ \bigcup_{V(T_2)}\tau\bigr)$ is the $(\mathcal T_j,\mathcal T_i)$-distinction.
--
--   This is the "standard tree-decomposition" relative to $\mathcal T_1,\dots,\mathcal T_n$: each tangle lives at its own node, and the tree separates any two tangles by their cheapest distinguishing separation. It yields that a hypergraph has at most $|V(G)|$ maximal tangles (10.4), and it is the counterpart, for many tangles at once, of the duality between tangles and tree-decompositions of small width.
--
--   **Formalization Note** $T$ is a tree on `Fin n` with $t_i=i$, which encodes $V(T)=\{t_1,\dots,t_n\}$ with distinct $t_i$. The orientation in (ii) is stated explicitly; it is the one forced by (i), since the $(\mathcal T_i,\mathcal T_j)$-distinction lies in $\mathcal T_i$. "The edge … of smallest $\lambda$-order" is quantified over every minimising edge of the path; by the first tie-breaker axiom any two such edges make the same separations. The tangles have their own orders, and $\Lambda$ is an arbitrary linearly ordered type.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 181, (10.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Tangle
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TreeDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_Laminar
import Definitions.Def_RobertsonSeymour1991_GM10_TangleTree_TieBreaker

namespace RobertsonSeymour1991.GM10.TangleTree

/-- (10.3), p. 181. Let `𝒯₁, …, 𝒯ₙ` (`n ≥ 1`) be mutually distinguishable tangles in `G`, of
orders `θ₁, …, θₙ`, and let `λ` be a tie-breaker. Then there is a tree-decomposition `(T, τ)` of
`G` with `V(T) = {t₁, …, tₙ}` (here `V(T) = Fin n`, `tᵢ = i`) such that
(i) for every edge `e = uw` of `T` and every `i` with `tᵢ` in the component of `T \ e`
containing `u`, the separation `(⋃_{t ∈ V(T₁)} τ(t), ⋃_{t ∈ V(T₂)} τ(t))` is not in `𝒯ᵢ`; and
(ii) for `i ≠ j`, if `e = uw` is an edge of the path of `T` between `tᵢ` and `tⱼ` making
separations of smallest `λ`-order on that path, with `tᵢ` on the `u` side, then the separation
made by `e` with `tⱼ`'s side first is the `(𝒯ᵢ, 𝒯ⱼ)`-distinction and the one with `tᵢ`'s side
first is the `(𝒯ⱼ, 𝒯ᵢ)`-distinction. -/
theorem result_10_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) {n : ℕ} (hn : 1 ≤ n)
    (θ : Fin n → ℕ) (𝒯 : Fin n → Set (G.Sub × G.Sub)) (h𝒯 : ∀ i, G.IsTangle (θ i) (𝒯 i))
    (hdist : ∀ i j, i ≠ j → ¬ 𝒯 i ⊆ 𝒯 j)
    {Λ : Type} [LinearOrder Λ] (lam : G.Sub × G.Sub → Λ) (hlam : G.IsTieBreaker lam) :
    ∃ D : TreeDecomposition G n,
      (∀ u w, D.T.Adj u w → ∀ i, i ∈ D.side u w → D.madeBy u w ∉ 𝒯 i) ∧
      (∀ i j, i ≠ j → ∀ p : D.T.Walk i j, p.IsPath → ∀ u w, s(u, w) ∈ p.edges →
        (∀ x y, s(x, y) ∈ p.edges → lam (D.madeBy u w) ≤ lam (D.madeBy x y)) →
        i ∈ D.side u w →
        Hypergraph.IsDistinction lam (𝒯 i) (𝒯 j) (D.madeBy w u).1 (D.madeBy w u).2 ∧
        Hypergraph.IsDistinction lam (𝒯 j) (𝒯 i) (D.madeBy u w).1 (D.madeBy u w).2) := by sorry

end RobertsonSeymour1991.GM10.TangleTree
