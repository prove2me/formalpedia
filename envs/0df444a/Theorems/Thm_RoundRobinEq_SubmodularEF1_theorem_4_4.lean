-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_theorem_4_4
-- name    : RoundRobinEq.SubmodularEF1.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:41.987001+00:00
-- url     : https://prove2.me/theorems/5325d47f-abf1-4cb2-ac36-dffcaa3faf1d
-- title:
--   Theorem 4.4 — for submodular valuations every α-approximate PNE of Round-Robin is α/3-EF1
-- statement:
--   Let $\alpha\in(0,1]$. Consider $n$ agents with non-decreasing, normalized, submodular valuations $v_1,\dots,v_n$ over a set $M$ of $m=kn$ goods, and let $\succ=(\succ_1,\dots,\succ_n)$ be an $\alpha$-approximate pure Nash equilibrium of the Round-Robin mechanism: every report is a ranking, and no agent can increase its true value by more than a factor $1/\alpha$ by reporting any other ranking. Then the allocation $(A_1,\dots,A_n)$ returned by Round-Robin$(\succ)$ is $\tfrac{\alpha}{3}$-EF1 with respect to the true valuations: for all agents $i,j$ with $A_j\neq\emptyset$ there is a good $g\in A_j$ with
--   $$v_i(A_i)\ \ge\ \frac{\alpha}{3}\cdot v_i(A_j\setminus\{g\}).$$
--
--   Round-Robin run on truthful additive reports is EF1, but agents with submodular valuations have incentives to misreport. The theorem shows that strategic behaviour costs only a constant factor of fairness: every approximate equilibrium remains approximately EF1, measured against the agents' real valuations.
--
--   **Formalization Note** Valuations are real-valued, normalized and non-decreasing (`IsValuation`) and submodular in the marginal form of p. 5 (`IsSubmodular`). The equilibrium hypothesis `IsApproxPNE α v σ` quantifies deviations over rankings only, as Definition 2.4 does; EF1 (`IsApproxEF1`) uses the true valuations `v i`, not the reports. $\alpha/3$ is a real division and $\alpha\in(0,1]$ is carried as `0 < α`, `α ≤ 1`.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 18, Theorem 4.4

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- Theorem 4.4, p. 18: for submodular valuations, every `α`-approximate PNE of Round-Robin
(`α ∈ (0, 1]`) is `α/3`-EF1 with respect to the true valuations. -/
theorem theorem_4_4 {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ) (hv : ∀ i, IsValuation (v i)) (hsub : ∀ i, IsSubmodular (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ) :
    IsApproxEF1 (α / 3) v (roundRobin σ) := by sorry

end RoundRobinEq.SubmodularEF1
