-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_3_3
-- name    : RobertsonSeymour1991.GM10.Minimax.result_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:10.348724+00:00
-- url     : https://prove2.me/theorems/834a9072-e370-4a1d-9789-17fa1f0725f2
-- title:
--   (3.3), pp. 161–162 — in an exact tree-labelling the leaf complements partition E − α(u, f)
-- statement:
--   Let $E$ be a finite set, $\kappa$ a connectivity function on $E$, $\mathcal A$ a set of efficient subsets of $E$, and $(T,\alpha)$ an exact tree-labelling over $\mathcal A$. Let $(u,f)$ be an incidence of $T$ and let $T_0$ be the component of $T\setminus f$ containing $u$. Then, as $(v,e)$ ranges over the incidences of $T$ with $v$ a leaf of $T$ and $v\in V(T_0)$, the sets $E-\alpha(v,e)$ are mutually disjoint and
--
--   $$\bigcup_{(v,e)}\bigl(E-\alpha(v,e)\bigr)=E-\alpha(u,f).$$
--
--   In particular the leaves of an exact tree-labelling partition $E$, which is how a branch-decomposition is read off.
--
--   **Formalization Note** The ground set $E$ is a finite type and subsets are `Set E`, with $E-X$ written as the complement. The hypotheses that $E$ is finite, that $\kappa$ is a connectivity function and that every member of $\mathcal A$ is efficient are the standing assumptions of §3 (p. 159), not additional ones. A tree-labelling stores the ternary tree on `Fin n` and the label of the incidence $(u,e)$, $e=uw$, as `α u w`; only adjacent pairs are ever used. The incidence $(u,f)$ is an adjacent pair $u,w$ with $f=uw$, and $T_0$ is the set of vertices reachable from $u$ in $T$ with the edge $uw$ deleted. A leaf has exactly one incidence, so disjointness is stated for distinct leaves.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 161–162, (3.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias

namespace RobertsonSeymour1991.GM10.Minimax

/-- (3.3), pp. 161–162: let `(T, α)` be an exact tree-labelling over `𝒜`, `(u, f)` an incidence of `T`
with `f = uw`, and `T₀` the component of `T\f` containing `u`. As `(v, e)` ranges over the incidences
of `T` with `v` a leaf of `T` in `V(T₀)` (here `e = vy`), the sets `E − α(v, e)` are mutually disjoint
and have union `E − α(u, f)`. -/
theorem result_3_3 {E : Type} [Finite E] (κ : Set E → ℤ) (hκ : IsConnectivityFunction κ)
    (𝒜 : Set (Set E)) (h𝒜 : ∀ X ∈ 𝒜, κ X ≤ 0) (n : ℕ) (L : TreeLabelling κ 𝒜 n) (hL : L.IsExact)
    (u w : Fin n) (huw : L.T.Adj u w) :
    (∀ v₁ y₁ v₂ y₂ : Fin n,
      (L.T.neighborSet v₁).ncard = 1 → L.T.Adj v₁ y₁ → (L.T.deleteEdges {s(u, w)}).Reachable u v₁ →
      (L.T.neighborSet v₂).ncard = 1 → L.T.Adj v₂ y₂ → (L.T.deleteEdges {s(u, w)}).Reachable u v₂ →
      v₁ ≠ v₂ → Disjoint (L.α v₁ y₁)ᶜ (L.α v₂ y₂)ᶜ) ∧
    {x : E | ∃ v y : Fin n, (L.T.neighborSet v).ncard = 1 ∧ L.T.Adj v y ∧
        (L.T.deleteEdges {s(u, w)}).Reachable u v ∧ x ∈ (L.α v y)ᶜ} = (L.α u w)ᶜ := by sorry

end RobertsonSeymour1991.GM10.Minimax
