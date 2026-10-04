-- Prove2me | Theorems.Thm_PolylogKServer_Rounding_rebalance
-- name    : PolylogKServer.Rounding.rebalance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:09:24.211867+00:00
-- url     : https://prove2.me/theorems/a0801a4b-8bd0-4b30-b2b8-5ec722fac121
-- title:
--   Lemma 25 — a consistent state can be made consistent and balanced at cost O(G(S, x))
-- statement:
--   For every $\sigma>5$ there is a constant $C>0$ such that the following holds. Let $T$ be a $\sigma$-HST whose leaves form the finite metric space $M$, let $x$ be a fractional k-server state on the leaves and let $S$ be a k-server state consistent with $x$ (not necessarily balanced). Then there is a k-server state $S'$ that is both consistent and balanced with respect to $x$, and the cost of changing $S$ to $S'$ satisfies
--   $$
--   \mathrm{cost}(S\to S')\ \le\ C\,G(S,x).
--   $$
--
--   The lemma is the repair step of the online rounding: after each elementary change of the fractional state, the paper restores balance at a cost proportional to the balance gap.
--
--   **Formalization Note** The $O(\cdot)$ is a constant depending on $\sigma$ only (the paper's proof gives $4\sigma/(\sigma-5)$), quantified after $\sigma$ and before the tree and the states. The cost of changing a state is the transportation cost of the definition `PolylogKServer.Rounding.States`. The fractional state satisfies $\sum_i x_i=k$, as on p. 36.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 37, Lemma 25

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer
import Definitions.Def_PolylogKServer_Rounding_States

namespace PolylogKServer.Rounding

open PolylogKServer.HST PolylogKServer.Fractional

/-- **Lemma 25** (arXiv:1110.1580v1, p. 37). For every `σ > 5` there is a constant `C > 0`
(depending on `σ` only) such that: if `T` is a σ-HST whose leaves form the metric space `M`,
`x` is a fractional k-server state and `S` is a k-server state consistent with `x`, then there
is a k-server state `S'` that is consistent and balanced with respect to `x`, and the cost of
changing `S` to `S'` is at most `C · G(S, x)`. -/
theorem rebalance :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (x : M → ℝ) (S : KConfig k M → ℝ),
        IsFracState k x → IsKState S → Consistent S x →
        ∃ S' : KConfig k M → ℝ, IsKState S' ∧ Consistent S' x ∧ Balanced T e x S' ∧
          transportCost S S' ≤ C * balanceGap T e S x := by sorry

end PolylogKServer.Rounding
