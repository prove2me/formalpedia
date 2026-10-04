-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_repair_count_geometric
-- name    : ServiceParts.Shortfall.repair_count_geometric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:44:16.795108+00:00
-- url     : https://prove2.me/theorems/293b4f79-0c1e-4164-97e3-f103c6c5b823
-- title:
--   Section 8.3.1 — the item-i count in the M/M/1 repair queue is geometric with η_i = λ_i/(µ − λ + λ_i)
-- statement:
--   In the M/M/1 repair system of Section 8.3.1, let $\lambda$ be the total arrival rate of reparable units, $\mu$ the repair rate, and $\lambda_i$ the arrival rate of item $i$, with
--   $$0 < \lambda_i \le \lambda < \mu .$$
--   Let $N$ be the number of units in the repair system and $N_i$ the number of item-$i$ units among them, and assume
--
--   1. $N$ is geometric: $P[N = j] = (1 - \rho)\rho^j$, $j \ge 0$, with $\rho = \lambda/\mu$;
--   2. given $N = j$, $N_i$ is binomial with parameters $j$ and $\lambda_i/\lambda$: $P[N = j, N_i = k] = P[N = j]\binom{j}{k}\left(\frac{\lambda_i}{\lambda}\right)^k\left(1 - \frac{\lambda_i}{\lambda}\right)^{j-k}$ for $k \le j$.
--
--   Then $N_i$ is geometric:
--   $$P[N_i = j] = (1 - \eta_i)\,\eta_i^{\,j}, \qquad \eta_i = \frac{\lambda_i}{\mu - \lambda + \lambda_i}, \qquad j = 0, 1, 2, \dots$$
--
--   The geometric law of the item count reduces the multi-item stock-level problem to independent single-item newsvendor problems with an explicit solution.
--
--   **Formalization Note** The page takes both hypotheses as known ("the system is a M/M/1 queueing system. As such, we know that N ... is geometrically distributed" and "as we discussed in Chapter 3, we know that $P[N_i = k \mid N = j]$ = binomial"); they are hypotheses here, and the multi-class FCFS queue itself is not built. The stability condition $\lambda < \mu$ is not written on the page but is needed for the geometric law; it is a hypothesis.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 202-204, Section 8.3.1 (geometric law of N_i, proved on pp. 203-204)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_RepairStock

open MeasureTheory

namespace ServiceParts.Shortfall

/-- Section 8.3.1, pp. 203–204. In the M/M/1 repair system with total arrival rate `λ`, repair
rate `µ > λ` and item-`i` arrival rate `0 < λ_i ≤ λ`, suppose the number `N` of units in the
repair system is geometric, `P[N = j] = (1 − ρ)ρ^j` with `ρ = λ/µ`, and, given `N = j`, the number
`N_i` of item-`i` units is binomial(`j`, `λ_i/λ`) (the Chapter 3 fact the page uses). Then `N_i` is
geometric: `P[N_i = j] = (1 − η_i)η_i^j` with `η_i = λ_i/(µ − λ + λ_i)`. -/
theorem repair_count_geometric {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (lamI lam mu : ℝ) (hlamI : 0 < lamI) (hlamI_le : lamI ≤ lam)
    (hstable : lam < mu) (N Ni : Ω → ℕ) (hN_meas : Measurable N) (hNi_meas : Measurable Ni)
    (hN : ∀ j : ℕ, (P {ω | N ω = j}).toReal = (1 - lam / mu) * (lam / mu) ^ j)
    (hthin : ∀ j k : ℕ, k ≤ j →
      (P {ω | N ω = j ∧ Ni ω = k}).toReal =
        (P {ω | N ω = j}).toReal *
          ((j.choose k : ℝ) * (lamI / lam) ^ k * (1 - lamI / lam) ^ (j - k))) :
    ∀ j : ℕ, (P {ω | Ni ω = j}).toReal = geomPMF (repairEta lamI lam mu) j := by sorry

end ServiceParts.Shortfall
