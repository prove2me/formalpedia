-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sigma_period_inverse_bounds
-- name    : WeierstrassEllipticZeta.sigma_period_inverse_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T23:00:46.412496+00:00
-- url     : https://prove2.me/theorems/920e803f-5913-468a-8ebb-d8af98ed88f6
-- title:
--   Reciprocal sigma powers along lattice progressions
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical zeta function $\zeta$. Let $\sigma$ be any normalized entire differential solution:
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,\qquad
--   \sigma'(z)=\zeta(z)\sigma(z)\quad(z\notin\Lambda).$$
--
--   Assume the canonical derivative identity $\zeta'(z)=-\wp(z)$ off the lattice. Then $\sigma(z)\ne0$ for every $z\notin\Lambda$. Moreover, for every fixed $u\notin\Lambda$ and every period $\omega\in\Lambda$, there is a real constant $C>0$ such that
--
--   $$
--   \left|\sigma(u+n\omega)^k\right|^{-1}
--   \le \exp\!\left(Ck(1+n^2)\right)
--   \qquad(n\in\mathbb Z,\ k\in\mathbb Z_{\ge0}).
--   $$
--
--   The constant is chosen before $n$ and $k$, and may depend on $L,\sigma,u,\omega$. Zero periods, negative translates, and the zeroth power are included. Every translated point remains outside the lattice. This supplies reciprocal-power bounds for sigma regularizers, including the period case of Kumar's auxiliary-value construction.
-- source:
--   Senthil Kumar K (2026), Section 5, equation (35) and the period case at the end of Lemma 10, especially the displayed sigma translation identity and the following reciprocal-power estimate, https://doi.org/10.1017/S001309152610145X. General integer translation law: DLMF 23.2.15 and 23.2.17, https://dlmf.nist.gov/23.2#E15. The bound exp(C*k*(1+n^2)) is the uniform coarse form used here, with C allowed to depend on the fixed base point and period.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.sigma_period_inverse_bounds
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    (∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) ∧
      ∀ u ω : ℂ, u ∉ L.lattice → ω ∈ L.lattice →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (k : ℕ),
          ‖D.sigma (u + n * ω) ^ k‖⁻¹ ≤
            Real.exp (C * k * (1 + (n : ℝ) ^ 2)) := by sorry
