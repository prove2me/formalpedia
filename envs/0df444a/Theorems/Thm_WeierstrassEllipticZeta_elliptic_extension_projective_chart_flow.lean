-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_flow
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_chart_flow
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T19:15:24.347757+00:00
-- url     : https://prove2.me/theorems/76c2a37d-b3a4-4819-8dfa-ab67f9f57bae
-- title:
--   Polynomial differential equations in both elliptic-extension charts
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and invariants $g_2,g_3$. Let $\sigma$ be entire, with $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'=\zeta\sigma$ off $\Lambda$, where $\zeta$ is the canonical Weierstrass zeta function. Let $S_0,\ldots,S_4$ be entire functions such that
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\qquad(z\notin\Lambda).$$
--
--   On the open set where $S_0\ne0$, put
--
--   $$x=\frac{S_1}{S_0},\qquad y=\frac{S_2}{S_0},\qquad t=\frac{S_3}{S_0}.$$
--
--   Then these functions have complex derivatives
--
--   $$x'=y,\qquad y'=6x^2-\frac{g_2}{2},\qquad t'=-x.$$
--
--   On the open set where $S_2\ne0$, put
--
--   $$a=\frac{S_0}{S_2},\qquad b=\frac{S_1}{S_2},\qquad d=\frac{S_4}{S_2}.$$
--
--   Their complex derivatives are
--
--   $$\begin{aligned}
--   a'&=-6b^2+\frac{g_2}{2}a^2,\\
--   b'&=-\frac12-g_2ab-\frac{3g_3}{2}a^2,\\
--   d'&=-2g_2b^2-3g_3ab.
--   \end{aligned}$$
--
--   Each assertion holds at every point where its specified denominator is nonzero, without excluding lattice points.
--
--   These polynomial differential equations describe the one-parameter curve in both charts of the elliptic-extension projective model. The second chart contains the fiber at infinity; the formulas extend through the apparent poles of the usual elliptic coordinates. No assumption that the five functions lack a common zero is required for the stated chartwise assertions. The theorem supplies differential equations for the parametrized curve, with no assertion here of an algebraic-group structure or a multiplicity bound.
-- source:
--   Derived by differentiating the one-parameter exponential curve in Senthil Kumar K (2026), Appendix A.2, the homogeneous and regular/lattice-point displays between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. The inputs are zeta-prime=-wp (DLMF 23.2.7, https://dlmf.nist.gov/23.2.E7), wp-double-prime=6wp^2-g2/2 (DLMF 23.3.12, https://dlmf.nist.gov/23.3.E12), and the cubic identity (DLMF 23.3.10, https://dlmf.nist.gov/23.3.E10). The second-chart equations are derived here by clearing denominators and using the entire identity theorem, not quoted as a theorem from the source.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_chart_flow
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z) := by sorry
