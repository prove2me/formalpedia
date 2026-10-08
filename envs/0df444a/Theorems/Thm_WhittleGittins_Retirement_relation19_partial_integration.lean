-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_relation19_partial_integration
-- name    : WhittleGittins.Retirement.relation19_partial_integration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:39.196061+00:00
-- url     : https://prove2.me/theorems/b7403f10-e812-4be8-95c6-706eefd19cad
-- title:
--   Relation (19) — F̂(x, s, M) = φᵢ(xᵢ, sᵢ, M) Pᵢ(x, s, M) + ∫_M^∞ φᵢ(xᵢ, sᵢ, m) d_m Pᵢ(x, s, m)
-- statement:
--   In Whittle's bandit process with per-project horizons $s$, let
--   $$\hat F(x, s, M) = K - \int_M^K \prod_j \frac{\partial \varphi_j(x_j, s_j, m)}{\partial m}\, dm \qquad (13)$$
--   and let $P_i(x, s, M) = \prod_{j\ne i}\partial\varphi_j(x_j, s_j, M)/\partial M$ as in (17). Then, for every project $i$ and every $M$, partial integration of (13) gives
--   $$\hat F(x, s, M) = \varphi_i(x_i, s_i, M)\, P_i(x, s, M) + \int_M^\infty \varphi_i(x_i, s_i, m)\, d_m P_i(x, s, m), \qquad (19)$$
--   where the last integral is the Lebesgue–Stieltjes integral over $m > M$ against the distribution function $P_i(x, s, \cdot)$.
--
--   Relation (19) expresses $\hat F$ as a mixture of single-project values, which is how the one-project dynamic programming equation (14) transfers to $\hat F$.
--
--   **Formalization Note** The Stieltjes measure $d_mP_i$ is supplied as the measure of any `StieltjesFunction` $G$ (a monotone right-continuous function) that agrees with $P_i(x, s, \cdot)$ everywhere; such a $G$ exists because right derivatives of convex functions are non-decreasing and right-continuous. The integral $\int_M^\infty$ is taken over the open half-line $(M, \infty)$, so a jump of $P_i$ at $M$ is accounted for by the first term. $\partial/\partial m$ is the right derivative.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 147 (PDF 5), Section 4, relation (19)

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (19) (p. 147), partial integration of (13):
`F̂(x, s, M) = φᵢ(xᵢ, sᵢ, M) Pᵢ(x, s, M) + ∫_M^∞ φᵢ(xᵢ, sᵢ, m) d_m Pᵢ(x, s, m)`, the Stieltjes
integral being taken against any Stieltjes function `G` that agrees with `Pᵢ(x, s, ·)`, over
`m > M`. -/
theorem relation19_partial_integration {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (i : Fin N) (M : ℝ)
    (G : StieltjesFunction ℝ) (hG : ∀ m, G m = Pdist B x s i m) :
    Fhat B x s M = phi B i (x i) (s i) M * Pdist B x s i M +
      ∫ m in Set.Ioi M, phi B i (x i) (s i) m ∂G.measure := by sorry

end WhittleGittins.Retirement
