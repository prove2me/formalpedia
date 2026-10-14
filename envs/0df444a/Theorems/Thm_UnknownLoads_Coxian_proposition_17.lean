-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_proposition_17
-- name    : UnknownLoads.Coxian.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:32.526866+00:00
-- url     : https://prove2.me/theorems/851234e8-e5b3-4074-a5b6-0ac854dfda02
-- title:
--   Proposition 17 — on Ω_T the total mass u_n converges uniformly on [0, T] to the infinite-server fluid function u of (3)
-- statement:
--   Let $\Omega_T$ be the set of nice sample paths of Proposition 16. For each $\omega \in \Omega_T$, the normalized total number of tasks $u_n(\omega) = \sum_{i\ge1} q_n(\omega,i)$ converges uniformly over $[0,T]$ to the function $u : [0,T] \to [0,\infty)$ defined in (3) by
--   $$u^m(0) := \sum_{i=0}^{\infty} \nu_i(m)\, s(0,\nu_i) \qquad\text{and}\qquad u(t) := \sum_{m=1}^{r} u^m(0)\, G_m(t) + \int_0^t \lambda\, G_1(t-s)\, ds,$$
--   where $s(0)$ is the limiting initial occupancy state and $G_m$ is the complementary distribution function of the residual service time of a task in phase $m$.
--
--   This is a strong law of large numbers for the total number of tasks under the coupled construction. Since $\ell_n = \lfloor u_n \rfloor_\Delta$ and $u(t) \to \rho$, it is what fixes the eventual value $\lfloor\rho\rfloor_\Delta$ of the threshold in Theorem 3.
--
--   **Formalization Note** "For each $\omega\in\Omega_T$" is rendered as: for every $B_T$ and $\omega$ with `IsNicePath sys T B_T ω`. $G_m(t) = (e^{tQ}\mathbf 1)_m$ with the Coxian sub-generator $Q$ (see the `Model` definition).
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 42, Proposition 17 (with (3), p. 14)

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_NicePaths
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Proposition 17 (p. 42). For each `ω ∈ Ω_T`, `u_n(ω) = Σ_{i≥1} q_n(ω, i)` converges uniformly
over `[0, T]` to the fluid function `u(t) = Σ_m u^m(0) G_m(t) + ∫_0^t λ G_1(t - s) ds` of (3). -/
theorem proposition_17 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (BT : ℕ) (ω : Ω) (hω : IsNicePath sys T BT ω) :
    TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => uMass (sys.s n ω t)) (fluidU P sys.sLim) atTop
      (Set.Icc 0 T) := by sorry

end UnknownLoads.Coxian
