-- Prove2me | Theorems.Thm_TreeMultiflow_Supplement_theorem_2_2
-- name    : TreeMultiflow.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:51:53.838438+00:00
-- url     : https://prove2.me/theorems/260172b8-06b0-412c-a4af-0ac0bc151029
-- title:
--   Theorem 2.2: leaf-to-leaf paths with load at most $4u_e+2$ split into eleven classes of load at most $u_e$
-- statement:
--   Let a tree have positive integer capacities $u_e$. Consider a finite collection of labeled paths, each joining two distinct leaves; repeated paths are allowed and are treated as distinct labeled objects. Suppose that every edge $e$ is used by at most $4u_e+2$ of the paths. Then there is a colouring
--   $$
--   c : \{\text{paths}\} \to \{1,\dots,11\}
--   $$
--   such that for every edge $e$ and every colour $i$,
--   $$
--   \bigl|\{p : c(p)=i,\ e\in p\}\bigr| \le u_e .
--   $$
--
--   This colouring theorem is the step that turns the Könemann–Parekh–Pritchard rounding (applied with capacities $4u_e$) into a feasible request set: one of the eleven colour classes carries at least $4/11$ of the rounded weight, which gives Theorem 1.1. Its ten-colour strengthening is the colouring step of Theorem 1.2.
--
--   **Formalization Note** The tree is a finite simple graph with `IsTree`; capacities are natural numbers on unordered vertex pairs, constrained to be at least one on the tree's edges. Paths are elements of a finite index type with endpoint maps $a,b$ (so repeated paths are distinct elements), each with $a(p)\ne b(p)$ and both endpoints leaves. Colours are `Fin 11`; a colour class is feasible when its load on every edge is at most $u_e$.
--
--   Differences from the source:
--   - encoding: a tree (finite) with a finite collection of labeled paths and eleven colours → [Fintype V], G.IsTree; a Fintype index type P with endpoints a, b; colours Fin 11; reason: same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 2.2, p.5

import Mathlib
import Definitions.Def_TreeMultiflow_load
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_IsLeaf

namespace TreeMultiflow.Supplement

/-- **Theorem 2.2: eleven colours.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 2.2,
p.5: "Let a tree have positive integer capacities uₑ. Consider a finite collection of labeled
paths, each joining two distinct leaves. Repeated paths are allowed and are treated as distinct
labeled objects. If at most 4uₑ + 2 paths use each edge e, then each path can be assigned one of
eleven colors so that, for every edge e and every color, at most uₑ paths of that color use e."

**Formalization Note.** The tree is finite (`[Fintype V]`), as for the ten-colour counterpart
`TreeMultiflow.theorem_2_2_ten`. Paths are a finite index type `P` with endpoints `a p ≠ b p`,
both leaves; repeated paths are distinct elements of `P`. Colours are `Fin 11`. The load
hypothesis is on every edge of the tree, as printed. Capacities `u : Sym2 V → ℕ` are constrained
(`1 ≤ u e`) only on edges of `G`. -/
theorem theorem_2_2 {V P : Type*} [Fintype V] [Fintype P] (G : SimpleGraph V)
    (hG : G.IsTree) (u : Sym2 V → ℕ) (hu : ∀ e ∈ G.edgeSet, 1 ≤ u e) (a b : P → V)
    (hP : ∀ p, a p ≠ b p ∧ IsLeaf G (a p) ∧ IsLeaf G (b p))
    (hload : ∀ e ∈ G.edgeSet, load G a b Finset.univ e ≤ 4 * u e + 2) :
    ∃ c : P → Fin 11, ∀ i : Fin 11, IsFeasible G u a b (Finset.univ.filter fun p => c p = i) := by sorry

end TreeMultiflow.Supplement
