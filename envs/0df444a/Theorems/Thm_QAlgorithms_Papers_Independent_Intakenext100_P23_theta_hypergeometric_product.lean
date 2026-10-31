-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_theta_hypergeometric_product
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.theta_hypergeometric_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:30:24.302454+00:00
-- url     : https://prove2.me/theorems/8014980c-9a94-4ff3-943f-e42b52f161bf
-- title:
--   Specialized theta–hypergeometric product identity
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   For $n\ge2$,
--   $$T(G)^2=\prod_{k=1}^{n-1}F_{k/n}(x).$$
--   This is the specialized product identity used to normalize the replica expression. The source proof invokes its unproved special assertion (B.5); that assertion is not assumed in the Lean theorem.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 13, Eq. (61), Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.13, Eq.(61), Appendix C pp.28--29. This is the specialized
hypergeometric product, not the general cited Thomae formula. Its source
argument invokes the unproved assertion (B.5). -/
theorem theta_hypergeometric_product (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : 0 < x ∧ x < 1) :
    theta0 (gammaMatrix n x) ^ 2 = hypergeometricProduct n x := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
