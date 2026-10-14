-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableEF1_theorem_4_5
-- name    : RoundRobinEq.CancelableEF1.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:24.636282+00:00
-- url     : https://prove2.me/theorems/f2c23489-3f17-4a11-904c-aee94d4294cc
-- title:
--   Theorem 4.5 — for subadditive cancelable valuations every α-approximate PNE of Round-Robin is α/2-EF1
-- statement:
--   Let $\alpha \in (0, 1]$. Consider $n \ge 1$ agents and $m$ goods, and suppose every agent $i$ has a valuation $v_i$ (normalized and non-decreasing) that is **subadditive**, $v_i(S \cup T) \le v_i(S) + v_i(T)$, and **cancelable**, $v_i(S \cup \{g\}) > v_i(T \cup \{g\}) \Rightarrow v_i(S) > v_i(T)$ for $g \notin S \cup T$. Let $\succ = (\succ_1, \dots, \succ_n)$ be an $\alpha$-approximate pure Nash equilibrium of the Round-Robin mechanism: for every agent $i$ and every total order $\succ'_i$ of the goods, $\alpha \cdot v_i(\mathrm{RR}(\succ'_i, \succ_{-i})_i) \le v_i(\mathrm{RR}(\succ)_i)$. Then the allocation $(A_1, \dots, A_n) = \mathrm{RR}(\succ)$ is $\alpha/2$-EF1 with respect to the true valuations: for all agents $i, j$ with $A_j \neq \emptyset$ there is a good $g \in A_j$ with
--   $$v_i(A_i) \ge \frac{\alpha}{2} \cdot v_i(A_j \setminus \{g\}).$$
--
--   Round-Robin with truthful rankings is known to give EF1 allocations for additive agents; this theorem says that fairness degrades gracefully when agents report strategically, as long as the reports form an approximate equilibrium. It covers additive, budget-additive and unit-demand valuations, among others.
--
--   **Formalization Note** The paper assumes $m = kn$ for some $k \in \mathbb{N}$ throughout (p. 7), noting that dummy goods reduce the general case to it; here $m = kn$ is a hypothesis and that reduction is not formalized. Deviations in the equilibrium hypothesis range over total orders only. Valuations are real-valued; non-negativity follows from normalization and monotonicity. Agents are 0-based (`Fin n`).
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 18, Theorem 4.5

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableEF1_Setting

namespace RoundRobinEq.CancelableEF1

/-- Theorem 4.5 (Amanatidis et al., arXiv:2301.13652v1, p. 18): for subadditive cancelable
valuations, every `α`-approximate PNE of Round-Robin (`α ∈ (0, 1]`) is `α/2`-EF1 with respect to
the true valuations. The standing assumption `m = k n` (p. 7) is carried as `hm`. -/
theorem theorem_4_5 {M : Type*} [DecidableEq M] [Fintype M] {n : ℕ} [NeZero n]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubadditive (v i) ∧ RoundRobinEq.CancelableBluff.IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ) :
    IsApproxEF1 (α / 2) v (roundRobin σ) := by sorry

end RoundRobinEq.CancelableEF1
