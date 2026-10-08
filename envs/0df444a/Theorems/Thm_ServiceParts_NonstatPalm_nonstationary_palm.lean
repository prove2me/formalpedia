-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_nonstationary_palm
-- name    : ServiceParts.NonstatPalm.nonstationary_palm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:17.251659+00:00
-- url     : https://prove2.me/theorems/20afa2d8-76f3-4b22-b6cb-2f7acb62c1c1
-- title:
--   Theorem 13 — Palm's theorem for nonstationary demand: units in resupply at t are Poisson with mean α(t)
-- statement:
--   Consider a single item at one location whose demands form a nonstationary Poisson process with rate $\lambda(s) \ge 0$, integrable on bounded intervals, starting with no demands at time $0$. A unit demanded at time $s$ has a resupply time with distribution function $G_s$, time dependent, with finite expectation; resupply times are independent from unit to unit and independent of the demand process. Let $X(t)$ be the number of units in resupply at time $t$, and
--   $$\alpha(t) = \int_0^t \bigl(1 - G_s(t-s)\bigr)\lambda(s)\,ds.$$
--   Then for every $t \ge 0$, $X(t)$ is Poisson distributed with mean $\alpha(t)$:
--   $$P\{X(t) = k\} = e^{-\alpha(t)}\,\frac{\alpha(t)^k}{k!}, \qquad k = 0, 1, 2, \dots$$
--
--   With a constant rate $\lambda$ and $G_s = G$ for every $s$, $\alpha(t) = \lambda\int_0^t (1 - G(u))\,du$ and the statement is the finite-time step of Palm's theorem; here the demand rate and the resupply-time distributions may both vary with time, and no limit is taken.
--
--   **Formalization Note** The demand process is the time change of a unit-rate Poisson process by $m(t) = \int_0^t \lambda$; resupply times are $\rho(T_k, U_k)$ for i.i.d. marks $U_k$ independent of the demand process, which realises any measurable family $G_s$ (see the model's definition). The hypothesis $t \ge 0$ is the book's range of time; for $t < 0$ the integral defining $\alpha(t)$ would be negative.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 216, Theorem 13 (proof pp. 216-217)

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem nonstationary_palm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (P {ω | S.unitsInResupply t ω = k}).toReal =
      Real.exp (-S.alpha t) * S.alpha t ^ k / (Nat.factorial k : ℝ) := by sorry

end ServiceParts.NonstatPalm
