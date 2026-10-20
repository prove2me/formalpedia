-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_oneShotConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P63.oneShotConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:41:25.375295+00:00
-- url     : https://prove2.me/theorems/1bd14623-2b47-4078-b46f-ca582b5fcb2d
-- title:
--   One-shot coding converse from approximate majorization
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Let $\mathcal N$ be any finite-dimensional quantum channel from a positive input dimension to a positive output dimension $D$, and let $\omega$ be a state on its output space. Let $0\le\varepsilon<1$ and $0\le\delta<1-\varepsilon$, and suppose $\delta_{\rm maj}(\mathcal N(\rho),\omega)\le\delta$ for every input state $\rho$. An $M$-message unassisted code consists of $M\ge1$ equiprobable input states and an $M$-outcome output POVM, with average error as in the usual trace formula. Every such code of average error at most $\varepsilon$ obeys
--
--   $$
--   \log M\le D_H^{\varepsilon+\delta}(\omega\|\pi_D),\quad \pi_D=I/D,\qquad D_H^\eta(X\|Y)=-\log\inf_{0\le Q\le I,\ \operatorname{Tr}(QX)\ge1-\eta}\operatorname{Tr}(QY).
--   $$
--
--   The type-II error is unnormalized. Against $\pi_D$ and with $\eta<1$ it is strictly positive, so the real logarithm is valid.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 10, Lemma 10, Eq. (59)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 10, Eq.(59), PDF pp.10–11. Arbitrary finite input/output dimensions;
pointwise spectral hypothesis replaces the equivalent maximum over input states. -/
theorem oneShotConverse (A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (N : Superop (Fin A) (Fin D)) (hN : IsChannel N)
    (Y : Mat (Fin D)) (hY : IsDensityMatrix Y) (e delta : ℝ)
    (he : 0 ≤ e) (heone : e < 1) (hdelta : 0 ≤ delta) (hdeltaone : delta < 1-e)
    (hdefect : ∀ X : Mat (Fin A), IsDensityMatrix X → defect (N X) Y ≤ delta)
    (M : ℕ) (C : Code (Fin A) (Fin D) M) (herror : averageError N C ≤ e) :
    logTwo M ≤ testingDivergence (e+delta) Y mixed := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
