-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_depot_units_poisson
-- name    : ServiceParts.NonstatPalm.depot_units_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:24.936293+00:00
-- url     : https://prove2.me/theorems/eb80b88f-5ffe-46e1-ba6f-ae6a1d6622a5
-- title:
--   Section 9.3.2 — with deterministic noncrossing depot repair times, units in depot resupply are Poisson with mean m₀(t̃, t)
-- statement:
--   In the two-echelon system of Section 9.3, failures at base $i$ form independent nonstationary Poisson processes with rates $\lambda_i$, each failure at base $i$ is sent to the depot with probability $1 - r_i$, independently, and a failure entering depot repair at time $u$ leaves it at $u + D(u)$, with $D \ge 0$ deterministic and satisfying $D(t) + t \ge D(s) + s$ for $s < t$. Let $X_0(t)$ be the number of units in the depot resupply system at time $t$, $\tilde t = \inf\{u \ge 0 : D(u) + u > t\}$ and
--   $$m_0(\tilde t, t) = \int_{\tilde t}^{t} \sum_i \lambda_i(u)(1 - r_i)\,du.$$
--   Then for every $t \ge 0$,
--   $$P\{X_0(t) = k\} = e^{-m_0(\tilde t, t)}\,\frac{m_0(\tilde t, t)^k}{k!}, \qquad k = 0, 1, 2, \dots$$
--
--   This distribution is the starting point of the book's depot backorder computations, $B_0(s_0(t)) = \sum_{x > s_0(t)} (x - s_0(t))P[X_0(t) = x]$, and of Eqs. (9.1)–(9.2).
--
--   **Formalization Note** The book's derivation also asserts that the depot sees a nonstationary Poisson process with rate $\lambda_0(t) = \sum_i \lambda_i(t)(1 - r_i)$; here that stream is not assumed but generated from the bases' failure processes and independent repair-location choices. The infimum defining $\tilde t$ is over $u \ge 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 220-221, Section 9.3.2

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_DepotSystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem depot_units_poisson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {nb : ℕ} (S : DepotSystem Ω P nb) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (P {ω | S.depotInResupply t ω = k}).toReal =
      Real.exp (-S.depotMean t) * S.depotMean t ^ k / (Nat.factorial k : ℝ) := by sorry

end ServiceParts.NonstatPalm
