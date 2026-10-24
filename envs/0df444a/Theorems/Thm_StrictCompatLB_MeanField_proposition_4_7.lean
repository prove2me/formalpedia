-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_proposition_4_7
-- name    : StrictCompatLB.MeanField.proposition_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:42.337636+00:00
-- url     : https://prove2.me/theorems/84a2d826-7edd-4542-87b4-5008953b3831
-- title:
--   Proposition 4.7 — under the optimal coupling, Σ|Q_i(K_{N,M}) − Q_i(G_N)| ≤ 2Δ_N
-- statement:
--   Fix $N\ge1$ and a policy $\Pi$ whose assignment function $p^\Pi$ is a Lipschitz continuous assignment probability function. Couple the $G_N$-system and the $K_{N,M}$-system by the optimal coupling. Let $z_n$ and $y_n$ be their states after $n$ events, and let $\Delta_N$ after $n$ events be the number of mismatches in queue length among the first $n$ events. If the inequality below holds initially (where $\Delta_N=0$), then after every number $n$ of events
--   $$\sum_{i=1}^\infty\big|Q_i(y_n)-Q_i(z_n)\big|\;\le\;2\,\Delta_N .$$
--
--   This converts the closeness of the two systems' occupancies into a count of routing mismatches, which the Lipschitz property then bounds.
--
--   **Formalization Note** The statement is pathwise: it holds for every sequence of events allowed by the coupling (`CoupledStep`), which is the paper's "almost surely, for all $t\ge0$", since both sides are piecewise constant and change only at events. The initial condition is written literally as the inequality at time $0$, $\sum_i|Q_i(y_0)-Q_i(z_0)|\le2\cdot0$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 18, Proposition 4.7, (4.7); pp. 17–18 (coupling); pp. 45–46, App. G

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Coupling

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Proposition 4.7 (p. 18; proof App. G, pp. 45–46), pathwise. Let `(z_n, y_n)` be the states of
the `G_N`-system and the `K_{N,M}`-system after `n` events of the optimal coupling, with
`mis j ∈ {0, 1}` the mismatch indicator of event `j`, so that `Δ_N = ∑_{j < n} mis j` after `n`
events. If `∑_{i ≥ 1} |Q_i(y_0) − Q_i(z_0)| ≤ 2Δ_N(0) = 0`, then after every number of events
`∑_{i ≥ 1} |Q_i(y_n) − Q_i(z_n)| ≤ 2 ∑_{j < n} mis j`. -/
theorem proposition_4_7 (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (hN : 1 ≤ N) (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (zs ys : ℕ → Fin N → ℕ) (mis : ℕ → ℕ)
    (hstep : ∀ n, CoupledStep M G N p (zs n) (ys n) (zs (n + 1)) (ys (n + 1)) (mis n))
    (h0 : occDiffSum (zs 0) (ys 0) ≤ 2 * ((∑ j ∈ Finset.range 0, mis j : ℕ) : ℝ)) :
    ∀ n : ℕ, occDiffSum (zs n) (ys n) ≤ 2 * ((∑ j ∈ Finset.range n, mis j : ℕ) : ℝ) := by sorry

end StrictCompatLB.MeanField
