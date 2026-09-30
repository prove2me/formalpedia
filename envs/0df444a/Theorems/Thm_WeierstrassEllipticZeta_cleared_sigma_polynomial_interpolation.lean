-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_sigma_polynomial_interpolation
-- name    : WeierstrassEllipticZeta.cleared_sigma_polynomial_interpolation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T01:08:43.849081+00:00
-- url     : https://prove2.me/theorems/dbf474ca-338a-443f-9cb2-7ba22a57994c
-- title:
--   Lemma 6(ii): cleared sigma polynomial interpolation
-- statement:
--   For a complex period lattice $\Lambda$, let $\wp,\zeta,\wp'$ denote its canonical Weierstrass functions. For positive integers $d,l$ and a complex coefficient array $p=(p_{ijk})$, set
--   $$P(w)=\sum_{i=0}^{d}\sum_{j,k=0}^{l}p_{ijk}w^i\wp(w)^j\zeta(w)^k.$$
--   The exponents are bounded separately by $(d,l,l)$; they need not attain these bounds. For a complex number $v$ put
--   $$M_1(v,l)=\max_{a,b,c\ge0,\ a+b+c\le5l}\left(1+|\zeta(v)^a\wp(v)^b\wp'(v)^c|\right).$$
--   The maximum is finite; its constant monomial contributes $2$.
--
--   Let $\sigma,S_0,S_1,S_2$ be entire functions for the fixed lattice, satisfying, off $\Lambda$,
--   $$S_0=\sigma\zeta,\qquad S_1=\sigma^2\wp,\qquad S_2=\sigma^3\wp'.$$
--   Assume that $A>0$ and, for every $z\in\mathbb C$,
--   $$|\sigma(z)|,\ |S_0(z)|,\ |S_1(z)|,\ |S_2(z)|\le\exp(A(1+|z|^2)).$$
--   No normalization or nonvanishing of $\sigma$ is assumed for this implication.
--
--   The following cleared-addition estimate holds with $R_0=1$ and $c_{14}=\exp(30A+128)$.
--
--   For every positive $d,l,M$, every array with $|p_{ijk}|\le M$, and every $v\notin\Lambda$, the expression
--   $$G(z)=\sigma(z)^{15l}[2(\wp(v)-\wp(z))]^{3l}P(z+v)$$
--   has an entire extension. Choose this extension before the radii and derivative data. If $2<r<R$, $R>R_0$, $|v|<R$, $|u|<r-2$, and $G$ has at least $N\ge0$ zeros counted with multiplicity in $|z|<r$, then for every integer $t\ge0$,
--   $$|G^{(t)}(u)|\le t!(d+1)(l+1)^2(5l+1)^6M(2R)^dM_1(v,l)c_{14}^{R^2l}\left(\frac{2r}{R}\right)^N.$$
--
--   This is the analytic-data form of Lemma 6(ii), retaining its precise factor at the fixed point.
--
--   **Formalization note.** A lower bound on the number of zeros is expressed by an arbitrary finite set $s\subset\{|z|<r\}$ and arbitrary multiplicities $m(a)\ge0$ with $N\le\sum_{a\in s}m(a)$, together with vanishing of every derivative of order below $m(a)$ at each $a\in s$. The estimate holds for every such witness. Empty sets, $N=0$, $t=0$, and the zero coefficient array are included. The product identities specify the extensions only where all meromorphic factors are regular: $z+u\notin\Lambda$ in the first case, and $z,z+v\notin\Lambda$ in the second. Zeros and derivative evaluation points may lie at excluded points of those product formulas, because they refer to the entire extensions. No condition $2r<R$ is imposed. The constants raised to $R^2l$ use real powers; all other displayed exponents are integers.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §4, Lemma 6(i)–(ii), equations (14)–(15) and the proof of Lemma 6.

import Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation

open Set WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_sigma_polynomial_interpolation
    (L : PeriodPair) (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (hrel : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A * (1 + ‖z‖^2)) ∧
      ∀ j, ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖^2))) :
    ClearedSigmaPolynomialInterpolation L σ (Real.exp (30*A+128)) 1 := by sorry
