-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_iidReference
-- name    : QAlgorithms.Papers.Independent.Information100.P63.iidReference
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:38:50.601252+00:00
-- url     : https://prove2.me/theorems/655dfd16-2c94-42ba-b573-03a569b470bc
-- title:
--   Approximate majorization for an i.i.d. reference
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   If $y_1,\ldots,y_D$ are the eigenvalues of $Y$, let $S_Y=-\log y_J$, where $\Pr(J=j)=y_j$; zero eigenvalues are never sampled. Define $q(Y)=\sup_{a\in\mathbb R}\Pr(a<S_Y\le a+1)$, which lies in $(0,1]$.
--
--   Let $\sigma$ be a fixed state on $\mathbb C^d$, $d\ge1$, whose spectral surprisal variance $V_\sigma=\sum_j y_j(-\log y_j-S(\sigma))^2$ is positive, where $S(\sigma)=-\sum_jy_j\log y_j$. There exist $\kappa_\sigma>0$ and $n_0\ge4$, depending only on $\sigma$, such that for every $n\ge n_0$ and every state $\rho$ on $(\mathbb C^d)^{\otimes n}$ satisfying $L_t(\rho)\ge L_t(\sigma^{\otimes n})$ for every $t>0$,
--
--   $$
--   \delta_{\rm maj}(\rho,\sigma^{\otimes n})\le\frac{\kappa_\sigma}{\sqrt n}(\log\log n+6).
--   $$
--
--   The comparison state need not be a channel output, and the fixed reference may be singular.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 9, Theorem 7, Eq. (49)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 7, Eq.(49), PDF p.9; the fixed reference may be singular. -/
theorem iidReference (d : ℕ) (hd : 0 < d) (Y : Mat (Fin d)) (hY : IsDensityMatrix Y)
    (hv : 0 < informationVariance Y) :
    ∃ k : ℝ, 0 < k ∧ ∃ n0 : ℕ, 4 ≤ n0 ∧ ∀ n ≥ n0,
      ∀ X : Mat (Fin n → Fin d), IsDensityMatrix X →
      (∀ t : ℝ, 0 < t → logDet t (tensorPower n Y) ≤ logDet t X) →
      defect X (tensorPower n Y) ≤ defectRate k n := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
