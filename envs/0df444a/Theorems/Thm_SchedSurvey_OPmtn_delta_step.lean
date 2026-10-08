-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_delta_step
-- name    : SchedSurvey.OPmtn.delta_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:56:43.43199+00:00
-- url     : https://prove2.me/theorems/1dcbd262-3c3c-4167-8276-ebc3e17f9979
-- title:
--   §5.2.2, p. 313 — the property (1)–(3) are designed for: reducing by an admissible δ lowers C by exactly δ
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $C$ be its largest row or column sum, $S$ a decrementing set of $P$, and $\delta>0$ a value satisfying the constraints (1), (2), (3) of §5.2.2. Let $P'$ be obtained from $P$ by replacing each $p_{ij}\in S$ by $\max\{0,p_{ij}-\delta\}$. Then $P'$ is nonnegative and its largest row or column sum is exactly $C-\delta$:
--
--   $$\max\Big\{\max_j \sum_i p'_{ij},\ \max_i \sum_j p'_{ij}\Big\}=C-\delta .$$
--
--   This is what makes the algorithm work: the partial schedule built from $S$ has length $\delta$, and the remaining work can still be finished in $C-\delta$ further time units, so joining the partial schedules gives a schedule of total length $C$. The survey states the property only through the constraints (1)–(3), which are designed for it.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. The conclusion is stated with the predicate `IsMaxLoad` of the model (all row and column sums of $P'$ are at most $C-\delta$, and one of them equals $C-\delta$). It holds for every $\delta>0$ satisfying (1)–(3), not only for the maximal one.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, constraints (1), (2), (3)

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313, the property the constraints (1)–(3) are designed for: if `S` is a
decrementing set and `δ > 0` satisfies (1), (2), (3), then `P′` (each `p_ij ∈ S` replaced by
`max{0, p_ij − δ}`) is nonnegative and its maximal row/column sum is exactly `C − δ`. -/
theorem delta_step {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (C : ℝ) (hC : IsMaxLoad P C) (S : Finset (Fin m × Fin n))
    (hS : IsDecrementingSet P C S) (δ : ℝ) (hδ : 0 < δ) (hadm : Admissible P C S δ) :
    IsMaxLoad (reduce P S δ) (C - δ) ∧ ∀ i j, 0 ≤ reduce P S δ i j := by sorry

end SchedSurvey.OPmtn
