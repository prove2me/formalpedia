-- Prove2me | Theorems.Thm_RunIntersect_Facet_proposition_4
-- name    : RunIntersect.Facet.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:25.252215+00:00
-- url     : https://prove2.me/theorems/f07fa968-adb7-48e7-89f0-fb0c1af089ea
-- title:
--   Proposition 4, p. 1016 — under conditions 1–3 a running intersection inequality defines a facet of MP_G for its support hypergraph G
-- statement:
--   Consider a running intersection inequality centered at an edge $e_0$ with neighbors $e_k$, $k\in K$ (a running intersection ordering of $\tilde E=\{e_0\cap e_k:k\in K\}$ and nodes $u_k\in N(e_0\cap e_k)$ fixed), and let $G$ be its support hypergraph, with node set $e_0\cup\bigcup_{k\in K}e_k$ and edge set $\{e_0\}\cup\{e_k:k\in K\}$. Assume:
--
--   1. $|e_0\cap e_k|\ge 2$ for every $k\in K$;
--   2. for every $K'\subseteq K$ with $e_0\cap\big(\bigcap_{k\in K'}e_k\big)\neq\emptyset$, we have $e_0\cap\big(e_i\setminus\bigcup_{k\in K'\setminus\{i\}}e_k\big)\neq\emptyset$ for all $i\in K'$;
--   3. each nonempty $N(e_0\cap e_k)$, $k\in K$, meets the set $U:=\{u_k:\ k\in K,\ N(e_0\cap e_k)\neq\emptyset\}$ in exactly one node.
--
--   Then the inequality
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset} z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k}e_k} z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\ \le\ \omega-1$$
--   defines a facet of $\mathrm{MP}_G$.
--
--   This is the paper's sufficient condition for running intersection inequalities to be facet-defining; combined with the lifting theorems of the earlier work it yields facets of multilinear polytopes of general hypergraphs.
--
--   **Formalization Note** The support hypergraph is built from $e_0$ and $K$ (the structural facts $|e_0|\ge 2$, $|e_k|\ge 2$ are arguments), and the inequality's data `d` is required to have center $e_0$ and neighbor set $K$; `d` carries $e_0\notin K$, adjacency, the ordering and the $u_k$. For $K'=\emptyset$ the intersection in condition 2 is the whole node type, so the hypothesis holds and the conclusion is vacuous; for $K'=\{i\}$ condition 2 reads $e_0\cap e_i\neq\emptyset$, which holds. "Defines a facet" means valid on $\mathrm{MP}_G$, with a nonempty face of dimension $\dim\mathrm{MP}_G-1$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1016, Proposition 4

import Mathlib
import Definitions.Def_RunIntersect_Facet_Setting

namespace RunIntersect.Facet

/-- Proposition 4, p. 1016. A running intersection inequality centered at `e0` with neighbors
`K`, satisfying conditions 1–3, defines a facet of the multilinear polytope of its support
hypergraph `G = (e₀ ∪ ⋃_k e_k, {e₀} ∪ K)`. -/
theorem proposition_4 {α : Type*} [Fintype α] [DecidableEq α]
    (e0 : Finset α) (K : Finset (Finset α))
    (he0 : 2 ≤ e0.card) (hK : ∀ k ∈ K, 2 ≤ k.card)
    (d : RIData (suppHg e0 K he0 hK)) (hd0 : d.e0 = e0) (hdK : d.K = K)
    (h1 : ∀ k ∈ K, 2 ≤ (e0 ∩ k).card)
    (h2 : ∀ K' ⊆ K, (e0 ∩ K'.inf id).Nonempty →
      ∀ i ∈ K', (e0 ∩ (i \ (K'.erase i).biUnion id)).Nonempty)
    (h3 : ∀ k ∈ K, (d.N k).Nonempty →
      (d.N k ∩ (K.filter (fun j => (d.N j).Nonempty)).image d.u).card = 1) :
    DefinesFacet (MP (suppHg e0 K he0 hK)) d.lhs d.rhs := by sorry

end RunIntersect.Facet
