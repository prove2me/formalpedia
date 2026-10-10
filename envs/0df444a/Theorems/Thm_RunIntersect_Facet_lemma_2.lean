-- Prove2me | Theorems.Thm_RunIntersect_Facet_lemma_2
-- name    : RunIntersect.Facet.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:27.151985+00:00
-- url     : https://prove2.me/theorems/070bd4db-036d-484f-b7d8-20bad0da6461
-- title:
--   Lemma 2, p. 1011 — components of a hypergraph with a running intersection ordering: n₀ + |{e : N(e) = ∅}|
-- statement:
--   Let $W$ be a finite node set and let $e_1,\dots,e_m$ be nonempty subsets of $W$ forming a running intersection ordering, with sets $N(e_1),\dots,N(e_m)$ as in (3). Then the hypergraph $(W,\{e_1,\dots,e_m\})$ has exactly
--   $$n_0+\big|\{k:\ N(e_k)=\emptyset\}\big|$$
--   connected components, where $n_0=\big|W\setminus\bigcup_k e_k\big|$ is the number of isolated nodes.
--
--   The lemma identifies the right-hand side $\omega-1$ of a running intersection inequality with the sum of its left-hand coefficients, and gives the component structure used in the proofs of Propositions 1 and 4.
--
--   **Formalization Note** The paper states the lemma for a hypergraph (edges of size at least two) but applies it to $\tilde G=(e_0,\tilde E)$, which may have loops and parallel edges. The Lean statement takes a list of **nonempty** subsets of $W$ (repetitions and singletons allowed), which covers both uses. The ordering is $0$-indexed, so $N(e_1)=\emptyset$ is the index $0$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1011, Lemma 2

import Mathlib
import Definitions.Def_RunIntersect_Facet_Setting

namespace RunIntersect.Facet

/-- Lemma 2, p. 1011. If `p_0, …, p_{m-1}` is a running intersection ordering of nonempty
subsets of `W`, the hypergraph `(W, {p_0, …, p_{m-1}})` has
`n₀ + |{k : N(p_k) = ∅}|` connected components, where `n₀ = |W ∖ ⋃_k p_k|` is the number of
isolated nodes. -/
theorem lemma_2 {α : Type*} [Fintype α] [DecidableEq α]
    (W : Finset α) (l : List (Finset α))
    (hsub : ∀ f ∈ l, f ⊆ W) (hne : ∀ f ∈ l, f.Nonempty) (hl : IsRIOrder l) :
    numComponents W (l : Multiset (Finset α)) =
      (W \ l.foldr (· ∪ ·) ∅).card +
        ((List.range l.length).filter (fun k => Nset l k = ∅)).length := by sorry

end RunIntersect.Facet
