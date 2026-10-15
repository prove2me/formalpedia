-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_theorem_2
-- name    : VehicleSharePricing.Static.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:13.849698+00:00
-- url     : https://prove2.me/theorems/dcf9ed42-6d1f-4a90-b1ee-34a7ea253375
-- title:
--   Theorem 2, p. 9 (static half) — $R(q^s)/R_s(q^s)\ge B^K_i(q^s)\ge B^K_i\ge K/(N+K-1+\Lambda/\mu)$, $B^K_i$ increasing in $i$
-- statement:
--   Consider a vehicle-sharing network with $N$ locations and $K\ge 1$ vehicles. Let $\Delta\ge K$, let $q^s$ be an optimal solution of Problem (2) that induces a strongly connected network and has $R_s(q^s)>0$, and let $r$ be a positive solution of the traffic equations (9). Put
--   $$\frac{\lambda}{\mu}=\sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q^s_{ij}}{\mu_{ij}},\qquad \Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij},\qquad \frac1\mu=\sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}}{\Lambda\mu_{ij}},$$
--   and define, with $B^j_0(q^s)=B^j_0=0$ for all $j\ge 0$,
--   $$B^K_i(q^s)=\frac{K}{N+K-1+\frac{\lambda}{\mu}\bigl(1-B^{K-1}_{i-1}(q^s)\bigr)},\qquad B^K_i=\frac{K}{N+K-1+\frac{\Lambda}{\mu}\bigl(1-B^{K-1}_{i-1}\bigr)}\qquad(i=1,\dots,K).$$
--   Then:
--
--   1. for every $i=1,2,\dots,K$,
--   $$\frac{R(q^s)}{R_s(q^s)}\ \ge\ B^K_i(q^s)\ \ge\ B^K_i\ \ge\ \frac{K}{N+K-1+\Lambda/\mu};$$
--   2. $B^K_{i+1}>B^K_i$ for every $i=1,2,\dots,K-1$.
--
--   The theorem turns the availability recursion (5) into a sequence of explicit, progressively tighter performance guarantees for static pricing; the weakest is the bound of Theorem 1, and the tightest, $B^K_K(q^s)$, is the exact ratio.
--
--   **Formalization Note** This is the static half of Theorem 2. The paper's first inequality, $R(q^s)/R(q^*)\ge R(q^s)/R_s(q^s)$, is Proposition 1 (p. 6); it compares with the optimal dynamic policy $q^*$, whose model (a controlled Markov chain with matrix-exponential trip stages) is not formalized in this mission, so it is not stated. The hypothesis $R_s(q^s)>0$ is added, since otherwise the ratio is $0/0$. The paper defines $B^j_0=0$ only for $j=1,\dots,K$ although $B^K_K$ uses $B^0_0$; it is taken to be $0$ as well. The availability inside $R$ is the BCMP product form of the definition file. Strictness of $B^K_i$ uses $\Lambda/\mu>0$, which follows from the nonempty demand set.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 9, Theorem 2

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability
import Definitions.Def_VehicleSharePricing_Static_BoundSeq

namespace VehicleSharePricing.Static

/-- Theorem 2, p. 9, static half. Let `q^s` be an optimal solution of Problem (2) with `Δ ≥ K`
that induces a strongly connected network and has `R_s(q^s) > 0`, let `r` be a positive solution
of (9), `λ/μ = ∑ Λ_ij q^s_ij / μ_ij`, `B^K_i(q^s) = Bseq N (λ/μ) K i` and
`B^K_i = Bseq N (Λ/μ) K i`. Then for every `i = 1, …, K`,
`R(q^s)/R_s(q^s) ≥ B^K_i(q^s) ≥ B^K_i ≥ K/(N + K − 1 + Λ/μ)`, and
`B^K_{i+1} > B^K_i` for every `i = 1, …, K − 1`. The first inequality of the paper,
`R(q^s)/R(q*) ≥ R(q^s)/R_s(q^s)` (Proposition 1), is not part of this statement. -/
theorem theorem_2 {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (K : ℕ) (hK : 1 ≤ K) (Δ : ℝ) (hΔ : (K : ℝ) ≤ Δ)
    (qs : L → L → ℝ) (hopt : IsStaticOptimal P Δ qs) (hconn : InducesStronglyConnected P qs)
    (hRs : 0 < Rs P qs) (r : L → ℝ) (hr : IsTrafficSolution P qs r) :
    (∀ i : ℕ, 1 ≤ i → i ≤ K →
      R P qs r K / Rs P qs ≥ Bseq (Fintype.card L) (workload P qs) K i ∧
      Bseq (Fintype.card L) (workload P qs) K i ≥
        Bseq (Fintype.card L) (demandWorkload P) K i ∧
      Bseq (Fintype.card L) (demandWorkload P) K i ≥
        (K : ℝ) / ((Fintype.card L : ℝ) + (K : ℝ) - 1 + demandWorkload P)) ∧
    (∀ i : ℕ, 1 ≤ i → i + 1 ≤ K →
      Bseq (Fintype.card L) (demandWorkload P) K (i + 1) >
        Bseq (Fintype.card L) (demandWorkload P) K i) := by sorry

end VehicleSharePricing.Static
