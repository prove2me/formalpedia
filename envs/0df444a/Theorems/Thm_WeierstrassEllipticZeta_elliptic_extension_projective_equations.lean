-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_equations
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T16:57:18.948137+00:00
-- url     : https://prove2.me/theorems/7d0bdb4e-d666-4a12-86ad-0435bfb26e63
-- title:
--   Homogeneous equations and algebraic-locus lift for the elliptic-extension projective map
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, invariants $g_2,g_3$, and normalized entire sigma differential data $\sigma$. Let $S_0,\ldots,S_4$ be entire functions satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\quad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map, and put
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}.$$
--
--   Suppose a projective map $P:E_\eta\to\mathbb P^4(\mathbb C)$ is given by the nonzero vectors
--
--   $$V(z,u)=(S_0(z),S_1(z),S_2(z),S_3(z)+uS_0(z),S_4(z)+uS_2(z)),
--   \qquad P([(z,u)])=[V(z,u)].$$
--
--   Define the polynomials in five variables
--
--   $$q(X)=X_0X_4-X_2X_3-2X_1^2,$$
--
--   $$c(X)=X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3.$$
--
--   They are homogeneous of degrees two and three, respectively. Every nonzero homogeneous representative $v$ of every point in the image of $P$ satisfies
--
--   $$q(v)=c(v)=0.$$
--
--   In particular, if $Z_{g_2,g_3}\subseteq\mathbb P^4(\mathbb C)$ is the locus cut out by these two equations, there exists a map
--
--   $$A:E_\eta\longrightarrow Z_{g_2,g_3}$$
--
--   whose composition with the inclusion is $P$. The assertion includes all lattice points and is independent of the choice of nonzero homogeneous representative. No injectivity, equality with the entire locus, dimension, smoothness or algebraic-group structure is asserted. The proof only needs the stipulated formula for $P$; it does not require a separate identification of $\eta$ with the canonical quasiperiod map.
-- source:
--   Derived from Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, the exponential-map coordinates between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X, and the Weierstrass differential equation, NIST DLMF 23.3.10, https://dlmf.nist.gov/23.3.E10. The quadratic relation follows by eliminating u+zeta from the displayed coordinates; the cubic is the homogenized differential equation. The derived statement asserts image containment and homogeneity, not equality with the entire locus or an algebraic-group embedding.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_equations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ))
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    extensionQuadric.IsHomogeneous 2 ∧ (extensionCubic L.g₂ L.g₃).IsHomogeneous 3 ∧
      (∀ (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0),
        Projectivization.mk ℂ v hv = P e →
          MvPolynomial.eval v extensionQuadric = 0 ∧
            MvPolynomial.eval v (extensionCubic L.g₂ L.g₃) = 0) ∧
      ∃ A : GraphQuotientExtension L.lattice η → ProjectiveExtensionLocus L.g₂ L.g₃,
        ∀ e, (A e).val = P e := by sorry
