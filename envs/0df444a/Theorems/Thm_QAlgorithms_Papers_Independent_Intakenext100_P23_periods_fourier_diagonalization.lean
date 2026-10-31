-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_periods_fourier_diagonalization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.periods_fourier_diagonalization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:28:39.347189+00:00
-- url     : https://prove2.me/theorems/a50c25f9-95e4-4007-829e-d55e6b0a65b0
-- title:
--   Fourier diagonalization, constant kernel, and positive deleted minors
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Assume $n\ge2$ and $\eta>0$. Let $\widetilde G$ be obtained by replacing $\beta$ with $\beta^{-1}$, and let $\Omega,\widetilde\Omega$ be the full $n$ by $n$ matrices with the same entries as $i\eta G,i\eta\widetilde G$. The matrix $U_{qr}=n^{-1/2}e^{2\pi iqr/n}$, with $1\le q,r\le n$, is unitary and simultaneously diagonalizes both matrices. Its eigenvalues are
--   $$\omega_q=2i\eta\sin(\pi q/n)\beta_{q/n},\quad \widetilde\omega_q=2i\eta\sin(\pi q/n)/\beta_{q/n}\quad(1\le q<n),\qquad \omega_n=\widetilde\omega_n=0.$$
--   Each full imaginary part is positive semidefinite and its kernel consists exactly of constant vectors. The deleted imaginary parts $G,\widetilde G$ are positive definite. The defining Gauss series converge, $F_{k/n}$ and $\beta_{k/n}$ are positive, and all positive multiples of the deleted matrices have convergent positive theta sums. These conclusions justify using the period matrices in the remaining identities.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 11, Eqs. (50)–(54),(56)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source pp.11--12, (50)--(54),(56): simultaneous unitary Fourier
diagonalization, a unique constant zero mode, and definite deleted minors.
Semidefiniteness and summability are conclusions, never extra hypotheses. -/
theorem periods_fourier_diagonalization (n : ℕ) (hn : 2 ≤ n) (eta x : ℝ)
    (heta : 0 < eta) (hx : 0 < x ∧ x < 1) :
    fourierMatrix n * (fourierMatrix n).conjTranspose = 1 ∧
    (fourierMatrix n).conjTranspose * fourierMatrix n = 1 ∧
    (∀ dual : Bool,
      fourierMatrix n * imaginaryMatrix (fullPeriod n eta x dual) *
        (fourierMatrix n).conjTranspose = Matrix.diagonal (periodEigenvalue n eta x dual)) ∧
    (∀ dual : Bool, (fullPeriod n eta x dual).PosSemidef ∧
      ∀ v : Fin n → ℝ, Matrix.mulVec (fullPeriod n eta x dual) v = 0 ↔
        ∃ a : ℝ, v = fun _ => a) ∧
    (gammaMatrix n x).PosDef ∧ (dualGammaMatrix n x).PosDef ∧
    (∀ k : Fin (n - 1),
      Summable (hypergeometricTerm (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) x) ∧
      0 < hypergeometricF (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) x ∧
      0 < hypergeometricRatio (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) x) ∧
    (∀ t : ℝ, 0 < t →
      Summable (thetaTerm (t • gammaMatrix n x)) ∧
      Summable (thetaTerm (t • dualGammaMatrix n x)) ∧
      0 < theta0 (t • gammaMatrix n x) ∧ 0 < theta0 (t • dualGammaMatrix n x)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
