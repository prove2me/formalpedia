-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_algebraic_auxiliary_values
-- name    : WeierstrassEllipticZeta.algebraic_auxiliary_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T11:22:16.032615+00:00
-- url     : https://prove2.me/theorems/4907aa60-48f7-4f47-b5e5-edb49e3d9e26
-- title:
--   Equation (18): algebraicity of the auxiliary elliptic data
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$ and canonical Weierstrass functions $\wp,\zeta$. Let $u_1,u_2\notin\Omega$ and $\omega,\theta\in\mathbb C$. Write $\eta(\omega)$ for the mission's fixed-base-point zeta increment. Suppose the ten values
--
--   $$
--   g_2,g_3,\omega,\eta(\omega),u_1,u_2,\wp(u_1),\zeta(u_1),\wp(u_2),\zeta(u_2)
--   $$
--
--   are algebraic over $\mathbb Q(\theta)$. Then all eighteen auxiliary values
--
--   $$
--   g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,
--   \zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),
--   $$
--
--   $$
--   \wp(u_i),\wp'(u_i),\wp''(u_i),\zeta(u_i)\quad(i=1,2)
--   $$
--
--   are algebraic over the same field. These are the data used in equation (18) to construct auxiliary functions. No transcendence assumption on $\theta$ or derivative-nonvanishing assumption at $u_1/2$ is required.
--
--   **Formalization Note.** Algebraicity is stated over $\mathbb Q[\theta]$. The second derivative is `deriv L.derivWeierstrassP`; the eighteen entries are listed in the source's order.
-- source:
--   Senthil Kumar K (2026), Section 5, algebraicity assertion immediately preceding equation (18); equations (5) and (17), and Section 4 Frobenius–Stickelberger identity; https://doi.org/10.1017/S001309152610145X. Formulated under regularity of u1,u2 and algebraicity of the ten values, the exact assumptions used for this step.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.Algebraic.Basic

namespace WeierstrassEllipticZeta

theorem algebraic_auxiliary_values
    (L : PeriodPair) (ω u₁ u₂ θ : ℂ)
    (hu₁ : u₁ ∉ L.lattice) (hu₂ : u₂ ∉ L.lattice)
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∀ i : Fin 18, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i) := by sorry

end WeierstrassEllipticZeta
