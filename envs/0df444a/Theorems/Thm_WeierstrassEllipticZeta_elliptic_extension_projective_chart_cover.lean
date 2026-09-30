-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_cover
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_chart_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T17:11:35.670654+00:00
-- url     : https://prove2.me/theorems/61c3c4b2-43c3-453e-b4f6-57ec6c9b82d8
-- title:
--   Two affine charts cover the elliptic-extension projective image
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and invariants $g_2,g_3$, and let $\sigma$ be normalized entire sigma differential data. Let $S_0,\ldots,S_4$ be entire functions with no common zero satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\quad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map and set
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}.$$
--
--   Define the projective locus
--
--   $$Z_{g_2,g_3}=\{[X]\in\mathbb P^4(\mathbb C):
--   X_0X_4-X_2X_3-2X_1^2=0,\quad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0\}.$$
--
--   Suppose a map $P:E_\eta\to Z_{g_2,g_3}$ has the following nonzero homogeneous coordinate vectors for all complex $z,u$:
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)].$$
--
--   Then the two entire coordinates never vanish simultaneously:
--
--   $$S_0(z)\ne0\quad\text{or}\quad S_2(z)\ne0\qquad(z\in\mathbb C).$$
--
--   Moreover, for every quotient point and every nonzero homogeneous representative $v$ of its projective image,
--
--   $$v_0\ne0\quad\text{or}\quad v_2\ne0.$$
--
--   Thus $P$ factors through the locus covered by these two standard affine charts:
--
--   $$Z^\circ_{g_2,g_3}=\{[X]\in Z_{g_2,g_3}:X_0\ne0\ \text{or}\ X_2\ne0\}.$$
--
--   There exists $A:E_\eta\to Z^\circ_{g_2,g_3}$ whose composition with the inclusion into $Z_{g_2,g_3}$ equals $P$ pointwise. The conclusion includes all lattice points and is independent of the choice of nonzero homogeneous representative. Neither surjectivity onto the chart locus nor an algebraic-group structure is asserted.
-- source:
--   Derived from Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, the regular and lattice-point forms of the exponential map between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. Those displays use projective coordinate zero off the lattice and coordinate two at lattice points. The proof establishes the two-chart cover directly from entire sigma derivative coordinates, using the proved canonical zeta derivative identity DLMF 23.2.7, https://dlmf.nist.gov/23.2.E7. It proves factorization through the chart locus, not a group-embedding theorem.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_chart_cover
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    (∀ z : ℂ, S 0 z ≠ 0 ∨ S 2 z ≠ 0) ∧
      (∀ (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0),
        Projectivization.mk ℂ v hv = (P e).val → v 0 ≠ 0 ∨ v 2 ≠ 0) ∧
      ∃ A : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃,
        ∀ e, (A e).val = P e := by sorry
