-- Prove2me | Theorems.Thm_RoughSurfaceScattering_lower_wavenumber_itp_bound
-- name    : RoughSurfaceScattering.lower_wavenumber_itp_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:44:03.21311+00:00
-- url     : https://prove2.me/theorems/bf84c088-236a-4060-81be-2c91dee8026d
-- title:
--   Theorem 6.1 (iii): interior transmission bound for the transmitted fields of hypersingular sources
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda}(\mathbb R)$ with $\lambda\in(0,1]$ describe the interface $\Gamma$, with $D^\pm$ the regions above and below it and $n$ the unit normal pointing into $D^-$. Let $k_+,\mu>0$ and let $k_{1,-}\ne k_{2,-}$ be positive lower wave numbers with
--
--   $$(\mu-1)(k_+^2-k_{m,-}^2\mu)\ge0,\qquad k_+^2\ne k_{m,-}^2\mu\qquad(m=1,2).$$
--
--   Suppose the point-source scattered fields of the two scatterers $(\Gamma,k_{m,-},k_+,\mu)$ agree: $u_{1,+}(x,y)=u_{2,+}(x,y)$ for all $x,y\in D^+$. Fix $x_0\in\Gamma$ and put $x_j=x_0-\frac\delta j\,n(x_0)$.
--
--   Then there is $\delta_1>0$ such that for every $\delta\in(0,\delta_1)$ there is a bounded $C^{2,\lambda}$ domain $D_0$ with
--
--   $$B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$$
--
--   with the following property: whenever $(\tilde u_{m,+}^{(j)},\tilde u_{m,-}^{(j)})$, $j\ge1$, solve the TSP for $(\Gamma,k_{m,-},k_+,\mu)$ with incident hypersingular point source $\nabla_x\Phi_{k_+}(\cdot,x_j)\cdot n(x_0)$, there is $C$ independent of $j$ with
--
--   $$\big\|\tilde u_{1,-}^{(j)}\big\|_{L^2(D_0)}\le C\qquad(j\ge1).$$
--
--   This is the key estimate of part (iii) of the proof of Theorem 6.1. The pair $(\tilde u_{1,-}^{(j)},\tilde u_{2,-}^{(j)})$ solves an interior transmission problem in $D_0$ whose boundary data vanish on $\partial D_0\cap\Gamma$. Since $k_{1,-}\ne k_{2,-}$, this problem is well posed on a sufficiently small $D_0$, which gives a bound uniform in $j$. Combined with Theorem 5.3 it contradicts the blow-up of $\nabla_x\Phi_0(\cdot,x_j)\cdot n(x_0)$ in $L^2(D_0)$.
--
--   **Formalization Note** $x_0=(s_0,f(s_0))$ and $n(x_0)$ is `normal f s0`. The scattered fields of the point sources are quantified over as families of TSP solutions indexed by the source point, as in Theorem 6.1. "$D_0$ sufficiently small" is stated as the existence of $D_0$ for every small $\delta$, with the same containments as in Theorem 5.3.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (iii), PDF p. 25, using the argument of part (ii), PDF pp. 24–25 (interior transmission problem (6.3), well-posedness on small D_0 by [10], bound ‖ũ_{1,-}^{(j)}‖_{L^2(D_0)} ≤ C).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem lower_wavenumber_itp_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ : ℝ) (hpar1 : ParamCond kp k1 μ) (hpar2 : ParamCond kp k2 μ) (hk : k1 ≠ k2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) (s0 : ℝ) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        ∀ u1 u2 : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k1 μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u1 j).1 (u1 j).2) →
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp k2 μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u2 j).1 (u2 j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j → l2Norm D0 (u1 j).2 ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
