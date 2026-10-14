-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableEF1_closing_bound
-- name    : RoundRobinEq.CancelableEF1.closing_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:17.193911+00:00
-- url     : https://prove2.me/theorems/81f647b3-b1b4-4ea9-9881-da2b45f8c078
-- title:
--   §4.2, p. 21 — v_i(A_j ∖ {y_1}) ≤ (2/α)·v_i(A_i) at an α-approximate PNE
-- statement:
--   Let $\alpha \in (0, 1]$, let all agents have subadditive cancelable valuations $v_1, \dots, v_n$ on $m = kn$ goods, and let $\succ$ be an $\alpha$-approximate pure Nash equilibrium of Round-Robin with allocation $(A_1, \dots, A_n)$. Fix agents $i \neq j$, a strict truthful ranking $\succ'_i$ of agent $i$, and let $y_1$ be the good of $A_j$ that is allocated first in Round-Robin$(\succ'_i, \succ_{-i})$. Then
--   $$v_i(A_j \setminus \{y_1\}) \le \frac{2}{\alpha} \cdot v_i(A_i).$$
--
--   This is the final bound of the proof of Theorem 4.5: it exhibits $y_1$ as the good whose removal makes agent $i$'s envy towards $j$ at most a factor $2/\alpha$, which is exactly $\alpha/2$-EF1 for the pair $(i, j)$.
--
--   **Formalization Note** $y_1$ is `y 0` for an enumeration `y` of $A_j$ by allocation time in the deviated run (`IsTimeEnum`). The strict truthful ranking may break ties among goods of equal singleton value in any way. $m = kn$ is a hypothesis (p. 7); the paper's reduction to it is not formalized.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 21, proof of Theorem 4.5, final display

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableEF1_Setting
import Definitions.Def_RoundRobinEq_CancelableEF1_DeviationOrders

namespace RoundRobinEq.CancelableEF1

/-- The closing bound of the proof of Theorem 4.5 (Amanatidis et al., arXiv:2301.13652v1, §4.2,
p. 21): under the hypotheses of Theorem 4.5, for agents `j ≠ i`, a strict truthful ranking `τ` of
agent `i`, and `y_1` the good of `A_j` allocated first in Round-Robin(τ, σ_{-i}),
`v_i(A_j \ {y_1}) ≤ (2/α) · v_i(A_i)`. -/
theorem closing_bound {M : Type*} [DecidableEq M] [Fintype M] {n : ℕ} [NeZero n]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubadditive (v i) ∧ RoundRobinEq.CancelableBluff.IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ)
    (i j : Fin n) (hji : j ≠ i)
    (τ : List M) (hτ : IsStrictTruthfulFor (v i) τ)
    (y : ℕ → M) (hy : IsTimeEnum (Function.update σ i τ) (roundRobin σ j) k y) :
    v i ((roundRobin σ j).erase (y 0)) ≤ 2 / α * v i (roundRobin σ i) := by sorry

end RoundRobinEq.CancelableEF1
