-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_depolarizingApproximateMajorization
-- name    : QAlgorithms.Papers.Independent.Information100.P63.depolarizingApproximateMajorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:40:00.421305+00:00
-- url     : https://prove2.me/theorems/a4c28a21-7930-405e-a428-3d585cae1b59
-- title:
--   Depolarizing approximate majorization, restated corollary
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $d\ge2$, $p_{\max}(d)=d^2/(d^2-1)$, and $\mathcal D_{p,d}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Define $\alpha=1-p+p/d$, $\beta=p/d$, and $\tau=\operatorname{diag}(\alpha,\beta,\ldots,\beta)$. The reference output after $n$ uses is $\tau^{\otimes n}=\mathcal D_{p,d}^{\otimes n}(|0^n\rangle\langle0^n|)$.
--
--   For fixed $0<p\le p_{\max}(d)$ with $p\ne1$, there are constants $\kappa>0$ and an integer $n_0\ge4$, depending only on $d,p$, such that for every $n\ge n_0$ and every state $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--
--   $$
--   \delta_{\rm maj}(\mathcal D_{p,d}^{\otimes n}(\rho),\tau^{\otimes n})\le\frac{\kappa}{\sqrt n}(\log\log n+6).
--   $$
--
--   The estimate is uniform over possibly entangled inputs and gives approximate spectral majorization.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 10, Corollary 8, Eq. (56)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 8, Eq.(56), PDF p.10. A distinct source result restating Theorem 1. -/
theorem depolarizingApproximateMajorization (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) (hpmax : p ≤ pMax d) (hpone : p ≠ 1) :
    ∃ k : ℝ, 0 < k ∧ ∃ n0 : ℕ, 4 ≤ n0 ∧ ∀ n ≥ n0,
      ∀ X : Mat (Fin n → Fin d), IsDensityMatrix X →
        defect (depolarizingN d n p X) (reference d n p) ≤ defectRate k n := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
