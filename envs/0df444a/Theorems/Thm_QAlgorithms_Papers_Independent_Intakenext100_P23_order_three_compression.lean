-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_order_three_compression
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.order_three_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:31:02.377782+00:00
-- url     : https://prove2.me/theorems/21e4a457-14ef-4199-beda-9a903d43476e
-- title:
--   Order-three theta compression and complex-boson expression
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Set $n=3$, let $t=\sqrt3\,\beta_{1/3}(x)$, and write $\vartheta_j(t)=\theta_j(it)$ for the standard Jacobi theta constants. Define
--   $$B(t)=\sum_{j=2}^4\vartheta_j(t)^2\vartheta_j(t/3)^2.$$
--   For $\eta>0$,
--   $$T(\eta G)^2=\tfrac12 B(\eta t),\qquad Q_3(\eta,x)^2=\frac{B(\eta t)B(t/\eta)}{4F_{1/3}(x)^4}.$$
--   The square of the real-field quotient is the complex-field expression in the source. All Jacobi constants are defined by their lattice sums.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 13, Section 4.3.2, Eqs. (63)–(64)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source pp.13--14, (63)--(64) and the following complex-field F_3 formula.
The real quotient is squared in the second clause, as required for c=2. -/
theorem order_three_compression (eta x : ℝ) (heta : 0 < eta)
    (hx : 0 < x ∧ x < 1) :
    let t := Real.sqrt 3 * hypergeometricRatio (1 / 3) x
    theta0 (eta • gammaMatrix 3 x) ^ 2 = thetaTriple (eta * t) / 2 ∧
    replicaFactor 3 eta x ^ 2 =
      thetaTriple (eta * t) * thetaTriple (t / eta) /
        (4 * hypergeometricF (1 / 3) x ^ 4) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
