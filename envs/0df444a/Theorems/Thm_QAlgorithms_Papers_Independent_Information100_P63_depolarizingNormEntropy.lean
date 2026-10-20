-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_depolarizingNormEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P63.depolarizingNormEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:40:55.433611+00:00
-- url     : https://prove2.me/theorems/9ec8d5e3-1166-4de8-8984-d0d0d8253129
-- title:
--   Schatten and entropy consequences for depolarizing outputs
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   For $n\ge1$, $0<p\le p_{\max}(d)$, and any state $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--
--   $$
--   \|\mathcal D_{p,d}^{\otimes n}(\rho)\|_q\le\|\tau^{\otimes n}\|_q\quad(1<q\le2),\qquad S(\mathcal D_{p,d}^{\otimes n}(\rho))\ge S(\tau^{\otimes n}).
--   $$
--
--   Here $\|X\|_q=(\sum_j\lambda_j(X)^q)^{1/q}$ and $S(X)=-\sum_j\lambda_j(X)\log\lambda_j(X)$. These are the consequences derived from log-determinant ordering; the separately cited full King inequality has a larger exponent range.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 6, Remark 5, Eqs. (28)–(29)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 5, Eqs.(28)–(29), PDF p.6. Only the consequence derived from log determinants
is asserted here: finite exponents `1<q≤2`, and von Neumann entropy. -/
theorem depolarizingNormEntropy (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p) (hpmax : p ≤ pMax d)
    (X : Mat (Fin n → Fin d)) (hX : IsDensityMatrix X) :
    (∀ q : ℝ, 1 < q → q ≤ 2 →
      schatten q (depolarizingN d n p X) ≤ schatten q (reference d n p)) ∧
    vnEntropy (reference d n p) ≤ vnEntropy (depolarizingN d n p X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
