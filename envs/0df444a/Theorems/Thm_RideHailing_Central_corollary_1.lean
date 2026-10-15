-- Prove2me | Theorems.Thm_RideHailing_Central_corollary_1
-- name    : RideHailing.Central.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:40.28122+00:00
-- url     : https://prove2.me/theorems/4d944456-73b5-41a9-b7af-ffc716929c97
-- title:
--   Corollary 1, p. 8 — under centralized control there is a unique participation equilibrium n_C and the two-step solution is optimal
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission (Assumptions 1–3, $0<\gamma<1$, $\bar\gamma p-c>0$, positive travel times, $p,N,c>0$). Let $\pi_C(n)$ be the per-driver profit of the two-step selected platform-optimal allocation of capacity $n$ (Proposition 1), $\Pi_C(n)$ the platform's optimal revenue at capacity $n$ (14), and $F$ the opportunity-cost distribution.
--
--   **Corollary 1 (Regime C: driver participation equilibrium and optimal solution).**
--   1. $\pi_C$ is continuous and nonincreasing on $(0,\infty)$, and strictly decreasing on $(n^C_1,\infty)$.
--   2. The participation equation has exactly one positive solution:
--   $$\exists!\,n_C>0:\qquad n_C=NF(\pi_C(n_C)).$$
--   3. $\pi_C$ is driver-optimal: for every $n\in(0,N]$, $\pi_C(n)=\max_{(s,r,q)\in\mathcal C_C(n)}\pi(s,r,n)$, the maximum being attained (condition (16) of Lemma 1).
--   4. For the solution $n_C$: $n_C<N$; $\Pi_C(n_C)$ is the maximum $\Pi^*_C$ of problem (13); and the two-step selection at $n_C$ is nonempty, each selected allocation together with $n_C$ being feasible for (13) and attaining $\Pi^*_C$.
--
--   In words, centralized control yields a unique equilibrium driver capacity, and solving first for the platform-optimal allocation of a fixed capacity and then for the equilibrium capacity gives the optimal solution of the platform's joint problem.
--
--   **Formalization Note** The page says "continuous and decreasing"; $\pi_C$ is constant equal to $\bar\gamma p-c$ on $(0,n^C_1]$, so "decreasing" is formalized as nonincreasing on $(0,\infty)$ plus strictly decreasing on $(n^C_1,\infty)$. "$n^*_C=n_C$ and $\Pi^*_C=\Pi_C(n_C)$" is formalized as attainment of the optimum of (13) at capacity $n_C$ by the two-step tuple; uniqueness of the optimal capacity is not claimed, since it can fail when $n_C>n^C_2$. Capacities are positive throughout because (12d) divides by $n$. $\pi_C$ is defined through the allocation problem, never by its closed form (18).
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, Corollary 1

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem corollary_1 (M : Model) (hM : M.Standing) :
    ContinuousOn M.piC (Set.Ioi 0) ∧ AntitoneOn M.piC (Set.Ioi 0) ∧
    StrictAntiOn M.piC (Set.Ioi M.nC1) ∧
    (∃! n : ℝ, 0 < n ∧ n = M.N * M.F (M.piC n)) ∧
    (∀ n, 0 < n → n ≤ M.N →
      IsGreatest ((fun x => M.prof x n) '' {x | M.InCC n x}) (M.piC n)) ∧
    (∀ nC, 0 < nC → nC = M.N * M.F (M.piC nC) →
      nC < M.N ∧
      IsGreatest {v | ∃ x n, M.Feas13 x n ∧ v = M.Rev x} (M.PiC nC) ∧
      (M.SelC nC).Nonempty ∧
      ∀ x ∈ M.SelC nC, M.Feas13 x nC ∧ M.Rev x = M.PiC nC) := by sorry
end RideHailing.Central
