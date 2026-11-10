-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_tree_automorphism_bound
-- name    : SmallClassesNeighbourhood.Linear.tree_automorphism_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:07.832208+00:00
-- url     : https://prove2.me/theorems/8ada319b-6185-41de-8e87-60b15a5cf4a2
-- title:
--   Section 2.3, Equation (1) — automorphisms of a bounded-degree tree
-- statement:
--   Let T be a finite tree on m vertices with maximum degree at most the integer Δ≥1. Its full automorphism group satisfies
--
--   $$|Aut(T)|\le m\Delta^{m-1}.$$
--
--   A tree is connected and nonempty. In particular, m=1 gives 1≤1. This is the source's uncoloured tree-automorphism bound used after Lemma 15.
--
--   Differences from the source: none.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Section 2.3, Equation (1), printed p. 11 (PDF p. 12)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem tree_automorphism_bound {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hdegree : ∀ v : V, Nat.card (T.neighborSet v) ≤ Δ) :
    Nat.card (T ≃g T) ≤ Fintype.card V * Δ ^ (Fintype.card V - 1) := by sorry

end SmallClassesNeighbourhood.Linear
