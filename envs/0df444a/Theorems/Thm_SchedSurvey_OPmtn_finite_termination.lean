-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_finite_termination
-- name    : SchedSurvey.OPmtn.finite_termination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:27.151995+00:00
-- url     : https://prove2.me/theorems/92b344d1-75bd-4894-b569-b189780361b1
-- title:
--   §5.2.2, p. 313 — the procedure reaches P′ = (0) after a finite number of steps
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $C$ be its largest row or column sum. Run the procedure of §5.2.2: put $P_0=P$; at stage $t$, if $P_t\ne 0$, choose a decrementing set $S_t$ of $P_t$ with respect to $C_t=C-(\delta_0+\dots+\delta_{t-1})$, let $\delta_t$ be the maximum subject to the constraints (1), (2), (3) for $P_t$, $C_t$, $S_t$, and let $P_{t+1}$ be obtained from $P_t$ by replacing each entry in $S_t$ by $\max\{0,p-\delta_t\}$. Then there is a number $N$, depending only on $P$, such that every run of the procedure has at most $N$ stages:
--
--   $$\exists N\ \ \forall \text{ runs } (P_t,S_t,\delta_t)_{t<k} \text{ with } P_t\ne 0 \text{ for all } t<k:\quad k\le N.$$
--
--   Together with the existence of decrementing sets this shows that the procedure stops, after finitely many stages, with $P'=(0)$, whatever decrementing sets are chosen.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. The current bound $C_t$ is written as $C$ minus the step lengths taken so far. The statement quantifies over every run, so it covers every choice of decrementing sets.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "… and repeat the procedure until after a finite number of times P′ = (0)."

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: "repeat the procedure until after a finite number of times P′ = (0)".
There is a bound `N` on the length of every run of the procedure: starting from `P₀ = P` with
`C₀ = C`, at each stage `t` with `P_t ≠ 0` choose a decrementing set `S_t` of `P_t` for
`C_t = C − (δ₀ + ⋯ + δ_{t−1})`, let `δ_t` be the maximum subject to (1), (2), (3), and put
`P_{t+1} = P_t′`. -/
theorem finite_termination {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (C : ℝ) (hC : IsMaxLoad P C) :
    ∃ N : ℕ, ∀ (k : ℕ) (Ps : ℕ → Fin m → Fin n → ℝ) (Ss : ℕ → Finset (Fin m × Fin n))
      (δs : ℕ → ℝ), Ps 0 = P →
      (∀ t < k, Ps t ≠ 0 ∧
        IsDecrementingSet (Ps t) (C - ∑ s ∈ Finset.range t, δs s) (Ss t) ∧
        IsMaxAdmissible (Ps t) (C - ∑ s ∈ Finset.range t, δs s) (Ss t) (δs t) ∧
        Ps (t + 1) = reduce (Ps t) (Ss t) (δs t)) →
      k ≤ N := by sorry

end SchedSurvey.OPmtn
