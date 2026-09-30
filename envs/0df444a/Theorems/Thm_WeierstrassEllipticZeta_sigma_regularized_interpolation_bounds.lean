-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_interpolation_bounds
-- name    : WeierstrassEllipticZeta.sigma_regularized_interpolation_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T01:08:48.333821+00:00
-- url     : https://prove2.me/theorems/3987dba1-ad7a-47df-a9e4-89f7596ca185
-- title:
--   Lemma 6: entire regularization and interpolation bounds
-- statement:
--   For every complex period lattice $\Lambda$ there exists a normalized entire sigma function $\sigma$ and real constants $R_0>0$, $c_{13}>1$, and $c_{14}>1$, chosen before all polynomial, radius, and derivative data, such that both estimates below hold. Normalization means $\sigma(0)=0$, $\sigma'(0)=1$, and $\sigma'(z)=\zeta(z)\sigma(z)$ off the lattice. The same sigma function and threshold $R_0$ serve both estimates.
--
--   For a complex period lattice $\Lambda$, let $\wp,\zeta,\wp'$ denote its canonical Weierstrass functions. For positive integers $d,l$ and a complex coefficient array $p=(p_{ijk})$, set
--   $$P(w)=\sum_{i=0}^{d}\sum_{j,k=0}^{l}p_{ijk}w^i\wp(w)^j\zeta(w)^k.$$
--   The exponents are bounded separately by $(d,l,l)$; they need not attain these bounds. For a complex number $v$ put
--   $$M_1(v,l)=\max_{a,b,c\ge0,\ a+b+c\le5l}\left(1+|\zeta(v)^a\wp(v)^b\wp'(v)^c|\right).$$
--   The maximum is finite; its constant monomial contributes $2$.
--
--   For every positive $d,l,M$, every array with $|p_{ijk}|\le M$, and every $u\in\mathbb C$, the expression
--   $$F(z)=\sigma(z+u)^{3l}P(z+u)$$
--   has an entire extension. Choose this extension before the radii and derivative data. If $2<r<R$, $R>R_0$, $|u|<R$, $|v|<r-2$, and $F$ has at least $N\ge0$ zeros counted with multiplicity in $|z|<r$, then for every integer $t\ge0$,
--   $$|F^{(t)}(v)|\le t!(d+1)(l+1)^2M(2R)^d c_{13}^{R^2l}\left(\frac{2r}{R}\right)^N.$$
--
--   For every positive $d,l,M$, every array with $|p_{ijk}|\le M$, and every $v\notin\Lambda$, the expression
--   $$G(z)=\sigma(z)^{15l}[2(\wp(v)-\wp(z))]^{3l}P(z+v)$$
--   has an entire extension. Choose this extension before the radii and derivative data. If $2<r<R$, $R>R_0$, $|v|<R$, $|u|<r-2$, and $G$ has at least $N\ge0$ zeros counted with multiplicity in $|z|<r$, then for every integer $t\ge0$,
--   $$|G^{(t)}(u)|\le t!(d+1)(l+1)^2(5l+1)^6M(2R)^dM_1(v,l)c_{14}^{R^2l}\left(\frac{2r}{R}\right)^N.$$
--
--   These are both analytic estimates of Lemma 6. They provide the entire functions and derivative bounds used for the auxiliary-polynomial argument, with no grid, arithmetic-model, or geometric zero-estimate assumption.
--
--   **Formalization note.** A lower bound on the number of zeros is expressed by an arbitrary finite set $s\subset\{|z|<r\}$ and arbitrary multiplicities $m(a)\ge0$ with $N\le\sum_{a\in s}m(a)$, together with vanishing of every derivative of order below $m(a)$ at each $a\in s$. The estimate holds for every such witness. Empty sets, $N=0$, $t=0$, and the zero coefficient array are included. The product identities specify the extensions only where all meromorphic factors are regular: $z+u\notin\Lambda$ in the first case, and $z,z+v\notin\Lambda$ in the second. Zeros and derivative evaluation points may lie at excluded points of those product formulas, because they refer to the entire extensions. No condition $2r<R$ is imposed. The constants raised to $R^2l$ use real powers; all other displayed exponents are integers.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://doi.org/10.1017/S001309152610145X, §4, Lemma 6(i)–(ii), equations (14)–(15) and the proof of Lemma 6.

import Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.sigma_regularized_interpolation_bounds
    (L : PeriodPair) :
    ∃ (D : EllipticSigmaDifferentialData L) (R₀ c₁₃ c₁₄ : ℝ),
      0 < R₀ ∧ 1 < c₁₃ ∧ 1 < c₁₄ ∧
      SigmaPolynomialInterpolation L D.sigma c₁₃ R₀ ∧
      ClearedSigmaPolynomialInterpolation L D.sigma c₁₄ R₀ := by sorry
