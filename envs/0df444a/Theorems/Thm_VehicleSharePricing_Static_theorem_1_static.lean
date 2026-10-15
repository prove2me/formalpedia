-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_theorem_1_static
-- name    : VehicleSharePricing.Static.theorem_1_static
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:11.284471+00:00
-- url     : https://prove2.me/theorems/462ccd91-08c1-4f18-8992-b59ba465fcb2
-- title:
--   Theorem 1, p. 7 (static half) — $R(q^s)/R_s(q^s)\ge K/(K+N-1+\Lambda/\mu)$
-- statement:
--   Consider a vehicle-sharing network with $N$ locations and $K\ge 1$ vehicles. Let $\Delta\ge K$, let $q^s$ be an optimal solution of Problem (2) that induces a strongly connected network and has $R_s(q^s)>0$, and let $r$ be a positive solution of the traffic equations (9). With $\Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}$ and $1/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}/(\Lambda\mu_{ij})$,
--   $$\frac{R(q^s)}{R_s(q^s)}\ \ge\ \frac{K}{K+N-1+\Lambda/\mu}.$$
--
--   The bound depends on the network only through $N$ and the demand-weighted travel load $\Lambda/\mu$, holds for every fleet size, and tends to $1$ at rate $O(1/K)$.
--
--   **Formalization Note** This is the static half of Theorem 1. The paper's first inequality, $R(q^s)/R(q^*)\ge R(q^s)/R_s(q^s)$, is Proposition 1 (p. 6); it compares with the optimal dynamic policy $q^*$, whose model (a controlled Markov chain with matrix-exponential trip stages) is not formalized in this mission, so it is not stated. The hypothesis $R_s(q^s)>0$ is added: otherwise the ratio is $0/0$. The availability inside $R$ is the BCMP product form of the definition file.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 7, Theorem 1

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

namespace VehicleSharePricing.Static

/-- Theorem 1, p. 7, static half: for an optimal solution `q^s` of Problem (2) with `Δ ≥ K`
that induces a strongly connected network and has `R_s(q^s) > 0`, and any positive solution `r`
of (9), `R(q^s)/R_s(q^s) ≥ K / (K + N − 1 + Λ/μ)`. The first inequality of the paper,
`R(q^s)/R(q*) ≥ R(q^s)/R_s(q^s)` (Proposition 1), is not part of this statement. -/
theorem theorem_1_static {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (K : ℕ) (hK : 1 ≤ K) (Δ : ℝ) (hΔ : (K : ℝ) ≤ Δ)
    (qs : L → L → ℝ) (hopt : IsStaticOptimal P Δ qs) (hconn : InducesStronglyConnected P qs)
    (hRs : 0 < Rs P qs) (r : L → ℝ) (hr : IsTrafficSolution P qs r) :
    R P qs r K / Rs P qs ≥
      (K : ℝ) / ((K : ℝ) + (Fintype.card L : ℝ) - 1 + demandWorkload P) := by sorry

end VehicleSharePricing.Static
