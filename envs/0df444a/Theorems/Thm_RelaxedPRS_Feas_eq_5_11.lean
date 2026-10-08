-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_eq_5_11
-- name    : RelaxedPRS.Feas.eq_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:41.076768+00:00
-- url     : https://prove2.me/theorems/c32398e7-f5cc-4075-b439-a62df9d1b190
-- title:
--   (5.11), proof of Theorem 5.1, p. 19 — d_{C_f∩C_g}(z⁺) ≤ C(γ_f, γ_g, λ, μ_ρ) d_{C_f∩C_g}(z)
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\neq\emptyset$, let $\gamma_f,\gamma_g>0$, $\lambda\in(0,1]$, $\mu>0$, and let $P_f=\mathbf{prox}_{\gamma_f d^2_{C_f}}$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$. Let $z\in\mathcal H$ satisfy the regularity inequality at $z$,
--   $$
--   d_{C_f\cap C_g}(z)\le\mu\max\{d_{C_f}(z),d_{C_g}(z)\},
--   $$
--   and let $z^+=(T^{\gamma_f,\gamma_g}_{\mathrm{PRS}})_\lambda(z)$. Then
--   $$
--   d_{C_f\cap C_g}(z^+)\le C(\gamma_f,\gamma_g,\lambda,\mu)\,d_{C_f\cap C_g}(z), \tag{5.11}
--   $$
--   where $C(\gamma_f,\gamma_g,\lambda,\mu)=\Big(1-\dfrac{4\lambda\min\{\gamma_g/(2\gamma_g+1)^2,\gamma_f/(2\gamma_f+1)^2\}}{\mu^2\max\{16\gamma_g^2/(2\gamma_g+1)^2,1\}}\Big)^{1/2}$.
--
--   This is the one-step contraction; Theorem 5.1 applies it along the iteration.
--
--   **Formalization Note** $\max\{c_1^2,1\}$ with $c_1=4\gamma_g/(2\gamma_g+1)$ is written as $\max\{16\gamma_g^2/(2\gamma_g+1)^2,1\}$. The square root is `Real.sqrt` (value $0$ on a negative radicand); a negative radicand forces $d_{C_f\cap C_g}(z)=0$, in which case $z^+=z$ and both sides vanish.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 19, proof of Theorem 5.1, (5.11)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proof of Theorem 5.1, (5.11), p. 19: one relaxed PRS step `z⁺ = (T^{γ_f,γ_g}_PRS)_λ(z)` with
`λ ∈ (0, 1]`, at a point `z` where `d_{C_f ∩ C_g}(z) ≤ μ max{d_{C_f}(z), d_{C_g}(z)}`, satisfies
`d_{C_f ∩ C_g}(z⁺) ≤ C(γ_f, γ_g, λ, μ) d_{C_f ∩ C_g}(z)`. -/
theorem eq_5_11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (γf γg : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (Pf Pg : H → H)
    (hPf : IsProx γf (dsq Cf) Pf) (hPg : IsProx γg (dsq Cg) Pg)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (μ : ℝ) (hμ : 0 < μ) (z : H)
    (hreg : Metric.infDist z (Cf ∩ Cg) ≤
      μ * max (Metric.infDist z Cf) (Metric.infDist z Cg)) :
    Metric.infDist (relaxOp (RelaxedPRS.StrongCvx.TPRS Pf Pg) t z) (Cf ∩ Cg) ≤
      Cfeas γf γg t μ * Metric.infDist z (Cf ∩ Cg) := by sorry

end RelaxedPRS.Feas
