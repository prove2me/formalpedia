-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_logDetNormEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P63.logDetNormEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:44:00.851567+00:00
-- url     : https://prove2.me/theorems/df8fe4c9-4346-4dc2-8a54-0a7cbc219a94
-- title:
--   Schatten and entropy consequences of log-determinant ordering
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $X,Y$ be states on the same space, and suppose $L_t(X)\ge L_t(Y)$ for every $t>0$. Then
--
--   $$
--   \|X\|_q\le\|Y\|_q\quad(1<q\le2),\qquad S(X)\ge S(Y),
--   $$
--
--   where $\|X\|_q=(\sum_j\lambda_j(X)^q)^{1/q}$ and $S(X)=-\sum_j\lambda_j(X)\log\lambda_j(X)$. This applies to arbitrary states, including singular states, without any channel premise.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 13, Proposition 11, Eqs. (69)–(70)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 11, Eqs.(69)–(70), PDF pp.13–14; arbitrary states, including singular ones. -/
theorem logDetNormEntropy (D : ℕ) (hD : 0 < D) (X Y : Mat (Fin D))
    (hX : IsDensityMatrix X) (hY : IsDensityMatrix Y)
    (horder : ∀ t : ℝ, 0 < t → logDet t Y ≤ logDet t X) :
    (∀ q : ℝ, 1 < q → q ≤ 2 → schatten q X ≤ schatten q Y) ∧
    vnEntropy Y ≤ vnEntropy X := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
