-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_varyingReference
-- name    : QAlgorithms.Papers.Independent.Information100.P63.varyingReference
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:38:13.061167+00:00
-- url     : https://prove2.me/theorems/5e289e3a-d786-4d29-9e4e-f05806e8f562
-- title:
--   Vanishing defect for varying reference states
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   If $y_1,\ldots,y_D$ are the eigenvalues of $Y$, let $S_Y=-\log y_J$, where $\Pr(J=j)=y_j$; zero eigenvalues are never sampled. Define $q(Y)=\sup_{a\in\mathbb R}\Pr(a<S_Y\le a+1)$, which lies in $(0,1]$.
--
--   There is an absolute constant $C>0$ with the following property. For each $n$, let $X_n,Y_n$ be states on a common positive finite-dimensional space of dimension $D_n$. Assume $L_t(X_n)\ge L_t(Y_n)$ for every $n$ and every $t>0$, and put $q_n=q(Y_n)$. If $q_n\to0$, then for all sufficiently large $n$,
--
--   $$
--   |\delta_{\rm maj}(X_n,Y_n)|\le Cq_n\left[1+\ln\ln\frac{e}{q_n}\right],\qquad \delta_{\rm maj}(X_n,Y_n)\longrightarrow0.
--   $$
--
--   No tensor structure is required. The concentration condition is sufficient; the explicit fixed-state counterexample is stated separately.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 9, Eq. (48)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq.(48), PDF p.9: universal implied constant and vanishing defect without tensor structure. -/
theorem varyingReference :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ → ℕ), (∀ n, 0 < D n) →
      ∀ (X Y : (n : ℕ) → Mat (Fin (D n))),
      (∀ n, IsDensityMatrix (X n)) → (∀ n, IsDensityMatrix (Y n)) →
      (∀ n, ∀ t : ℝ, 0 < t → logDet t (Y n) ≤ logDet t (X n)) →
      Tendsto (fun n => concentration (Y n)) atTop (nhds 0) →
      (∃ n0 : ℕ, ∀ n ≥ n0, |defect (X n) (Y n)| ≤
        C * (concentration (Y n) * (1 + Real.log (Real.log (Real.exp 1 / concentration (Y n)))))) ∧
      Tendsto (fun n => defect (X n) (Y n)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
