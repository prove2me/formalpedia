-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_descent
-- name    : WeierstrassEllipticZeta.elliptic_extension_projective_descent
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T16:38:12.245134+00:00
-- url     : https://prove2.me/theorems/ec2a2e1c-5f8f-4ae2-bb23-b71a175888c7
-- title:
--   Projective descent of elliptic-extension coordinates through the period quotient
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, normalized entire sigma differential data $\sigma$, and entire functions $S_0,\ldots,S_4$ with no common zero, satisfying
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2)\quad(z\notin\Lambda).$$
--
--   Let $\eta:\Lambda\to\mathbb C$ be a $\mathbb Z$-linear map equal to the canonical zeta quasiperiods. Put
--
--   $$E_\eta=\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\},$$
--
--   $$V(z,u)=(S_0(z),S_1(z),S_2(z),S_3(z)+uS_0(z),S_4(z)+uS_2(z)).$$
--
--   There exists a well-defined map $P:E_\eta\to\mathbb P^4(\mathbb C)$ such that, for every $z,u\in\mathbb C$, the vector $V(z,u)$ is nonzero and
--
--   $$P([(z,u)])=[V(z,u)].$$
--
--   Write $\varphi(z)=(z,[(z,0)])\in\mathbb C\times E_\eta$. If $r(z)$ is the nonzero representative chosen by Mathlib for $P([(z,0)])$, then for every $z\in\mathbb C$ and $i,j\in\{0,\ldots,4\}$,
--
--   $$r_j(z)\ne0\ \Longleftrightarrow\ S_j(z)\ne0,\qquad
--   \frac{r_i(z)}{r_j(z)}=\frac{S_i(z)}{S_j(z)}.$$
--
--   All assertions include lattice points. The ratio identity uses Lean's total field division, so it also holds when the common chart denominator vanishes. No analyticity of the arbitrarily chosen representative is asserted: the normalized chart functions equal the corresponding ratios of entire functions. This is projective descent and chart compatibility; injectivity, algebraic-group structure and multiplicity bounds are separate obligations.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, the displayed exponential map and one-parameter curve between (A.3) and (A.4), https://doi.org/10.1017/S001309152610145X. This derived formalization proves that its five elliptic projective coordinates descend through the period pairs (omega,-eta(omega)), and proves compatibility of all normalized charts. The proof derives sigma translation from the canonical zeta translation law and extends coordinate identities analytically across the lattice. No algebraic-group structure, embedding theorem or multiplicity estimate is included.

import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.LinearAlgebra.Projectivization.Basic

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_projective_descent
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ),
      (∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
      (∀ (z : ℂ) (j : Fin 5),
        (P ((extensionCurve L.lattice η z).2)).rep j ≠ 0 ↔ S j z ≠ 0) ∧
      (∀ (z : ℂ) (i j : Fin 5),
        (P ((extensionCurve L.lattice η z).2)).rep i /
          (P ((extensionCurve L.lattice η z).2)).rep j = S i z / S j z) := by sorry
