-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_surjective
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T18:53:24.323834+00:00
-- url     : https://prove2.me/theorems/c55b7438-ce97-4dc9-bd5b-4720988baa1f
-- title:
--   Surjectivity of the elliptic-extension projective parametrization
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and invariants $g_2,g_3$. Let $\sigma$ be an entire function satisfying $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'(z)=\zeta(z)\sigma(z)$ off $\Lambda$, where $\zeta$ is the canonical Weierstrass zeta function. Let $S_0,\ldots,S_4$ be entire functions without a common zero, satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\qquad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map, and put
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\},\qquad i(u)=[(0,u)].$$
--
--   Let $Z^\circ_{g_2,g_3}$ be the locus in $\mathbb P^4(\mathbb C)$ defined by
--
--   $$X_0X_4-X_2X_3-2X_1^2=0,\qquad
--   X_0X_2^2-4X_1^3+g_2X_0^2X_1+g_3X_0^3=0,\qquad
--   X_0\ne0\text{ or }X_2\ne0.$$
--
--   Suppose $P:E_\eta\to Z^\circ_{g_2,g_3}$ has nonzero homogeneous vectors
--
--   $$P([(z,u)])=[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)]$$
--
--   for all complex $z,u$. Equip this locus with a projective additive-fiber model $(\pi,A)$: the map $\pi([X])=[X_0:X_1:X_2]$ has exactly the projective Weierstrass cubic as image, and
--
--   $$A(u,[X])=[X_0:X_1:X_2:X_3+uX_0:X_4+uX_2]$$
--
--   obeys the additive action laws and is simply transitive on every fiber of $\pi$. Assume $P(e+i(u))=A(u,P(e))$ for all $e,u$.
--
--   Then $P$ is surjective:
--
--   $$\forall q\in Z^\circ_{g_2,g_3},\quad\exists e\in E_\eta,\quad P(e)=q.$$
--
--   Thus every point of the two-chart locus is represented by the stipulated homogeneous parametrization, including the full fiber above the point at infinity of the Weierstrass cubic. The proof establishes pointwise surjectivity. The complete algebraic-group identification and the geometric multiplicity estimate remain separate obligations. No separate canonical-quasiperiod hypothesis on $\eta$ is needed: existence of the stipulated equivariant map is among the assumptions.
-- source:
--   Derived from the elliptic-extension embedding and exponential map in Senthil Kumar K (2026), Appendix A.2, exact sequence (A.3) and the homogeneous, regular and lattice-point displays between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. The elliptic-curve parametrization is described in DLMF 23.20(ii), https://dlmf.nist.gov/23.20#ii. The proof derives surjectivity of wp from its double poles and periodicity (DLMF 23.2(ii)-(iii), https://dlmf.nist.gov/23.2#ii) using the reciprocal omitted-value argument and Liouville, then the cubic equation and oddness of wp-prime, and finally the additive-fiber action. This is the pointwise surjectivity component of the source geometry.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_surjective
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e)) :
    Function.Surjective P := by sorry
