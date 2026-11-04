-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_fluid_u_limits
-- name    : UnknownLoads.Coxian.fluid_u_limits
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T20:44:40.497028+00:00
-- url     : https://prove2.me/theorems/058a4394-f19c-4d8e-aed4-6691a593ad45
-- title:
--   Fluid function of the Coxian model: u is differentiable, u(t) → ρ and u̇(t) → 0
-- statement:
--   Let $u$ be the fluid function (3) of the Coxian scenario with constant arrival rate $\lambda$:
--   $$u(t) = \sum_{m=1}^{r} u^m(0)\, G_m(t) + \int_0^t \lambda\, G_1(t-s)\, ds, \qquad u^m(0) = \sum_{\nu} \nu(m)\, s(0,\nu),$$
--   where $G_m(t) = (e^{tQ}\mathbf 1)_m$ is the complementary cumulative distribution function of the residual service time of a task currently in phase $m$, $Q$ being the sub-generator of the Coxian phase process ($Q_{mm} = -\mu_m$, $Q_{m,m+1} = p_m\mu_m$). Let $\rho = \lambda/\mu$ be the offered load, with $1/\mu = \sum_{i=1}^r (1-p_i)\prod_{j<i}p_j \sum_{k\le i} 1/\mu_k$ the mean service time.
--
--   Then, for any initial state $s(0) \in S$, the function $u$ is differentiable at every $t > 0$, and
--   $$\lim_{t\to\infty} u(t) = \rho, \qquad \lim_{t\to\infty} \dot u(t) = 0.$$
--
--   This is the analytic fact about $u$ invoked at the start of the proof of Theorem 3 ("It follows from (3) that $u$ is differentiable. Furthermore, $u(t)\to\rho$ and $\dot u(t)\to 0$ as $t\to\infty$"). It holds because $G_m(t)\to 0$ exponentially fast for every phase $m$ (the sub-generator $Q$ is upper bidiagonal with negative diagonal), while $\int_0^\infty G_1 = 1/\mu$ is the mean of the Coxian service time and $\dot u(t) = \sum_m u^m(0)\dot G_m(t) + \lambda G_1(t)$.
--
--   Formalization note: phases are indexed by `Fin r`; `phaseMass0` is a `tsum`, so if it diverges it takes the junk value $0$, which does not affect the claim since $G_m(t) \to 0$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 44, proof of Theorem 3 (first paragraph), with u defined in (3), p. 14, and Proposition 17, p. 42

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Model
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Proof of Theorem 3 (p. 44): the fluid function `u` of (3) (with constant `λ`) is
differentiable, `u(t) → ρ` and `u̇(t) → 0` as `t → ∞`. -/
theorem fluid_u_limits {P : Params} (s0 : Profile P.r → ℝ) (hs0 : InS s0) :
    (∀ t : ℝ, 0 < t → DifferentiableAt ℝ (fluidU P s0) t) ∧
    Tendsto (fluidU P s0) atTop (𝓝 (rho P)) ∧
    Tendsto (deriv (fluidU P s0)) atTop (𝓝 0) := by sorry

end UnknownLoads.Coxian
