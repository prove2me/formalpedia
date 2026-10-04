-- Prove2me | Theorems.Thm_ServiceParts_Palm_integral_tail_tendsto_mean
-- name    : ServiceParts.Palm.integral_tail_tendsto_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T22:34:34.981978+00:00
-- url     : https://prove2.me/theorems/278b4671-e581-48d0-b886-8a3ef379ca65
-- title:
--   Eq. (3.10) — ∫₀ᵗ[1 − G(u)]du tends to the mean resupply time τ̄
-- statement:
--   Let $L$ be the resupply time of the $(s-1,s)$ system: nonnegative, with density, distribution function $G$ and finite mean $\bar\tau$. Then
--   $$\lim_{t\to\infty}\int_0^t [1 - G(u)]\,du = \int_0^\infty [1-G(u)]\,du = \bar\tau.$$
--
--   This identity turns the finite-time mean $\lambda\int_0^t[1-G]$ of Eq. (3.8) into the steady-state mean $\lambda\bar\tau$ of Palm's theorem.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 41, Eq. (3.10)

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem integral_tail_tendsto_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    Tendsto (fun t : ℝ => ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) atTop
      (𝓝 S.meanResupply) := by sorry

end ServiceParts.Palm
