-- Prove2me | Theorems.Thm_TreeMultiflow_theorem_2_2_ten
-- name    : TreeMultiflow.theorem_2_2_ten
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:06.695225+00:00
-- url     : https://prove2.me/theorems/63e14823-b3bd-4182-8f47-d9f5036d1a37
-- title:
--   Theorem 2.2 with ten colours: at most $4u_e+2$ leaf-to-leaf paths per edge split into ten classes of load at most $u_e$
-- statement:
--   Let a tree have positive integer capacities $u_e$. Consider a finite collection of labeled paths, each joining two distinct leaves; repeated paths are allowed and are treated as distinct labeled objects. If at most $4u_e+2$ paths use each edge $e$, then each path can be assigned one of **ten** colours so that, for every edge $e$ and every colour, at most $u_e$ paths of that colour use $e$.
--
--   This is Theorem 2.2 (p.5) with eleven colours replaced by ten, as used in the proof of Theorem 1.2 (p.11): "Form the initial bins as in the proof of Theorem 2.2, and apply Theorem 5.2. The resulting ten color classes respect the original capacities."
--
--   Differences from the source:
--   - reading: Form the initial bins as in the proof of Theorem 2.2, and apply Theorem 5.2. The resulting ten color classes respect the original capacities (p.11) → Theorem 2.2's statement (p.5) with ten colours in place of eleven; reason: this is the colouring step the proof of Theorem 1.2 asserts; the bins of p.6 satisfy (i)–(iii) of Theorem 3.1 under Theorem 2.2's load bound
--   - encoding: a tree (finite) and a finite collection of labeled paths → [Fintype V], G.IsTree; a Fintype index type P with endpoints a, b; ten colours as Fin 10; reason: same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, proof of Theorem 1.2, p.11, with Theorem 2.2, p.5 and the bin formation in the proof of Theorem 2.2, p.6

import Mathlib
import Definitions.Def_TreeMultiflow_load
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_IsLeaf

namespace TreeMultiflow

/-- **Theorem 2.2 with ten colours.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, proof of
Theorem 1.2, p.11: "Form the initial bins as in the proof of Theorem 2.2, and apply Theorem 5.2.
The resulting ten color classes respect the original capacities." This is Theorem 2.2 (p.5) with
eleven colours replaced by ten: "Let a tree have positive integer capacities uₑ. Consider a finite
collection of labeled paths, each joining two distinct leaves. Repeated paths are allowed and are
treated as distinct labeled objects. If at most 4uₑ + 2 paths use each edge e, then each path can be
assigned one of eleven colors so that, for every edge e and every color, at most uₑ paths of that
color use e."

**Formalization Note.** The tree is finite (`[Fintype V]`). Paths are a finite index type `P`
with endpoints `a p ≠ b p`, both leaves; repeated paths are distinct elements of `P`. The load
hypothesis is on every edge, as in Theorem 2.2 (not only on internal edges). -/
theorem theorem_2_2_ten {V P : Type*} [Fintype V] [Fintype P] (G : SimpleGraph V)
    (hG : G.IsTree) (u : Sym2 V → ℕ) (hu : ∀ e ∈ G.edgeSet, 1 ≤ u e) (a b : P → V)
    (hP : ∀ p, a p ≠ b p ∧ IsLeaf G (a p) ∧ IsLeaf G (b p))
    (hload : ∀ e ∈ G.edgeSet, load G a b Finset.univ e ≤ 4 * u e + 2) :
    ∃ c : P → Fin 10, ∀ i : Fin 10, IsFeasible G u a b (Finset.univ.filter fun p => c p = i) := by sorry

end TreeMultiflow
