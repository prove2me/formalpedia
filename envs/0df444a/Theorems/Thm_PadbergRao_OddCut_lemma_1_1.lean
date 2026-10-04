-- Prove2me | Theorems.Thm_PadbergRao_OddCut_lemma_1_1
-- name    : PadbergRao.OddCut.lemma_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:59:48.855192+00:00
-- url     : https://prove2.me/theorems/81c0bd64-517e-4f1a-b462-2d77dfc9e805
-- title:
--   Lemma 1.1 — some odd minimum cut-set lies on one side of a minimum odd-pair cut-set
-- statement:
--   Let $G = (V, E)$ be a finite undirected graph without loops and multiple edges, with edge weights $c_e \ge 0$. Let $V_1 \subseteq V$ be a nonempty set of odd-labelled nodes, $V_0 = V - V_1$ the even-labelled nodes, and assume that the total label $\lambda(V)$ is even, i.e. $|V_1|$ is even. Let $(M : V - M)$ be a minimum cut-set with respect to all pairs of odd labelled nodes in $G$. Then there exists an odd minimum cut-set $(X : V - X)$ in $G$ such that
--
--   $$
--   X \subseteq M \quad \text{or} \quad X \subseteq V - M .
--   $$
--
--   In Hu's terminology, every cut-set that is minimum with respect to all pairs of odd nodes admits a noncrossing odd minimum cut-set. This is what allows the odd minimum cut-set problem to be solved by a modification of the Gomory–Hu procedure.
--
--   **Formalization Note** The graph is a symmetric nonnegative weight function `c : V → V → ℝ` (weight `0` for a non-edge) over a `Fintype V`; $V_1$ is a `Finset` `odd` with `odd.Nonempty` and `Even odd.card`. "Odd minimum cut-set" is `IsOddMinCut`, minimizing over all node sets with $\lambda$ odd.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 68, Lemma 1.1

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity
import Definitions.Def_PadbergRao_OddCut_IsOddMinCut
import Definitions.Def_PadbergRao_OddCut_IsMinOddPairCut

namespace PadbergRao.OddCut

/-- Lemma 1.1 (Padberg–Rao 1982, p. 68). If `(M : V − M)` is a minimum cut-set with respect to
all pairs of odd labelled nodes, some odd minimum cut-set `(X : V − X)` has `X ⊆ M` or
`X ⊆ V − M`. -/
theorem lemma_1_1 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (hodd_ne : odd.Nonempty) (hodd_even : Even odd.card)
    (M : Finset V) (hM : IsMinOddPairCut c odd M) :
    ∃ X : Finset V, IsOddMinCut c odd X ∧ (X ⊆ M ∨ X ⊆ Mᶜ) := by sorry

end PadbergRao.OddCut
