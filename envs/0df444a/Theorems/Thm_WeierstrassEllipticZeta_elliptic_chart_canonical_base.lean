-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_canonical_base
-- name    : WeierstrassEllipticZeta.elliptic_chart_canonical_base
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T20:35:29.24985+00:00
-- url     : https://prove2.me/theorems/01bb01fc-6322-444b-839a-37cd3f2d51bb
-- title:
--   Canonical chart base ideals have height at least two and terminal contact
-- statement:
--   Fix a complex period pair $L$, its canonical Weierstrass functions and normalized entire sigma differential data $D$. Let the five entire functions $S_j$ agree away from the period lattice with
--
--   $$S(z)=\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2).$$
--
--   Let $Q\in\mathbb C[Y_0,\ldots,Y_6]$ be homogeneous of degree $n$ in its last five variables. Suppose its entire pullback
--
--   $$w\longmapsto Q(1,w,S_0(w),S_1(w),S_2(w),S_3(w),S_4(w))$$
--
--   is not identically zero. Choose one of the two affine charts $j\in\{0,1\}$ and a point $z$ with nonzero denominator, respectively $S_0(z)$ or $S_2(z)$. Write
--
--   $$v_0(w)=(w,S_1/S_0,S_2/S_0,S_3/S_0),\qquad
--   v_1(w)=(w,S_0/S_2,S_1/S_2,S_4/S_2),$$
--
--   with the ratios evaluated at $w$. In $A=\mathbb C[T,X_1,X_2,X_3]$ the normalized equations are
--
--   $$Q_0(t,x,y,u)=Q(1,t,1,x,y,u,yu+2x^2),$$
--   $$Q_1(t,a,b,h)=Q(1,t,a,b,1,ah-2b^2,h).$$
--
--   Set
--
--   $$K_{j,z}=\{r\in A:r(v_j(w))=0\text{ for all }w\text{ in some neighborhood of }z\},
--   \qquad J_{j,z,Q}=K_{j,z}+(Q_j).$$
--
--   For a natural number $T$, assume the projective chart pullback of $Q$, obtained by dividing all five $S$ coordinates by the chosen denominator, has analytic order at least $T+1$ at $z$. Then
--
--   $$\operatorname{ht}(J_{j,z,Q})\ge2,\qquad Q_j\in J_{j,z,Q},\qquad
--   P_T(J_{j,z,Q})\subseteq\ker(\operatorname{eval}_{v_j(z)}).$$
--
--   Here $P_T$ uses the fixed chart derivation, given on coordinates by
--
--   $$\delta_0(t,x,y,u)=(1,y,6x^2-g_2/2,-x),$$
--   $$\delta_1(t,a,b,h)=(1,-6b^2+(g_2/2)a^2,
--   -1/2-g_2ab-(3g_3/2)a^2,-2g_2b^2-3g_3ab).$$
--
--   **Formalization Note.** This constructs the algebraic input for the previously proved component-selection criterion. The starting ideal follows the pattern of adjoining the polynomial equation to a relation ideal in [Philippon (1986), §5, p. 380](https://www.numdam.org/item/10.24033/bsmf.2060.pdf), within the framework of [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). The chosen relation ideal is explicitly the local analytic-orbit kernel. Its identification with the full algebraic-group ideal is not asserted. The theorem does not select a global stabilizer locus or prove a uniform degree budget.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, p. 380: starting ideal obtained by adjoining the polynomial equation to an ambient relation ideal, and derivative ideals contained in evaluation ideals at points of high vanishing. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The complete theorem constructs the canonical base from the local analytic-orbit kernel and the normalized polynomial, and proves height at least two, membership and terminal derivative containment in both Weierstrass charts. Identification of this germ kernel with the entire algebraic-group ideal is not asserted. The remaining child must select the locus and chart points and prove a uniform total-length degree budget for this specific base ideal; no converse for arbitrary previous bases is claimed.

import Definitions.Def_WeierstrassEllipticZeta_ChartOrbitBase

open MvPolynomial WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_chart_canonical_base
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun w : ℂ => eval
      ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) ≠ 0)
    (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0)
    (T : ℕ)
    (horder : ((T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
      (fun w : ℂ => eval ![1, w, S 0 w / S (extensionChartDenominator c) w,
        S 1 w / S (extensionChartDenominator c) w,
        S 2 w / S (extensionChartDenominator c) w,
        S 3 w / S (extensionChartDenominator c) w,
        S 4 w / S (extensionChartDenominator c) w] Q) z) :
    (2 : ℕ∞) ≤ (extensionChartBaseIdeal S Q c z).height ∧
      extensionChartNormalize c Q ∈ extensionChartBaseIdeal S Q c z ∧
      TranscendenceTheory.differentialProlongation (extensionChartDerivation L.g₂ L.g₃ c)
        (extensionChartBaseIdeal S Q c z) T ≤
          RingHom.ker (eval (extensionChartCoordinates S c z)) := by sorry
