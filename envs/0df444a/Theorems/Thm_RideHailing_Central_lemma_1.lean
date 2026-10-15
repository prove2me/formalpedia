-- Prove2me | Theorems.Thm_RideHailing_Central_lemma_1
-- name    : RideHailing.Central.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:29.845949+00:00
-- url     : https://prove2.me/theorems/1e3c8c4a-4358-4617-81e4-4a3f1bf5b2c6
-- title:
--   Lemma 1, p. 8 (regime C) — if π_C is driver-optimal (16), the two-step solution attains the optimal revenue Π*_C = Π_C(n_C)
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission. Problem (13) maximizes the revenue $\Pi(s)=\gamma p\bar s$ over tuples $(s,r,q,n)$ with $n>0$, $(s,r,q)\in\mathcal C_C(n)$ and $n=NF(\pi(s,r,n))$; its optimal value is $\Pi^*_C$. The two-step solution computes $\Pi_C(n)=\max\{\Pi(s):(s,r,q)\in\mathcal C_C(n)\}$ and the per-driver profit $\pi_C(n)$ of the selected allocation, and then solves the participation equation $n_C=NF(\pi_C(n_C))$.
--
--   **Lemma 1 (regime C).** Suppose that
--   1. the platform-optimal solution is also driver-optimal at every capacity: for every $n\in(0,N]$,
--   $$\pi_C(n)=\max_{(s,r,q)\in\mathcal C_C(n)}\pi(s,r,n), \tag{16}$$
--   the maximum being attained;
--   2. $\pi_C$ is nonincreasing on $(0,N]$ (Step 2 of the two-step approach);
--   3. $n_C>0$ solves $n_C=NF(\pi_C(n_C))$.
--
--   Then $\Pi_C(n_C)$ is the maximum of problem (13), i.e. $\Pi^*_C=\Pi_C(n_C)$, and every two-step selected allocation $(s,r,q)$ of capacity $n_C$, together with $n_C$, is feasible for (13) and attains $\Pi^*_C$.
--
--   The lemma links optimality of the two-step solution to the alignment of platform and driver incentives; Corollary 1 verifies its hypotheses in regime $C$.
--
--   **Formalization Note** The paper states Lemma 1 for each regime $X\in\{C,M,A\}$; only $X=C$ is posed, since $\mathcal C_M$ and $\mathcal C_A$ rely on objects given only in the e-companion. Monotonicity of $\pi_C$ is the hypothesis the two-step procedure (14)–(15) presupposes (Step 2), made explicit. "$n^*_C=n_C$" is formalized as "the optimum of (13) is attained at capacity $n_C$"; uniqueness of the optimal capacity is not claimed, because it can fail when $n_C>n^C_2$ (wasteful repositioning keeps the revenue $\gamma p\bar S$ at a smaller capacity). (16) is posed for $n\in(0,N]$ since (12d) divides by $n$.
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, Lemma 1 (with (13)–(16), pp. 7–8)

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem lemma_1 (M : Model) (hM : M.Standing)
    (h16 : ∀ n, 0 < n → n ≤ M.N →
      IsGreatest ((fun x => M.prof x n) '' {x | M.InCC n x}) (M.piC n))
    (hanti : AntitoneOn M.piC (Set.Ioc 0 M.N))
    (nC : ℝ) (hnC0 : 0 < nC) (hnC : nC = M.N * M.F (M.piC nC)) :
    IsGreatest {v | ∃ x n, M.Feas13 x n ∧ v = M.Rev x} (M.PiC nC) ∧
      ∀ x ∈ M.SelC nC, M.Feas13 x nC ∧ M.Rev x = M.PiC nC := by sorry
end RideHailing.Central
