-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_special_theta_invariance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.special_theta_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:29:12.787809+00:00
-- url     : https://prove2.me/theorems/d12d6cc2-3fb5-43ed-b919-7232ddecb0c6
-- title:
--   Special theta invariance for the paper-specific Fourier matrix
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Assume $n\ge2$ and $\eta>0$. Let $\widehat U$ be the upper left $(n-1)$ by $(n-1)$ block of the normalized Fourier matrix and $H=\operatorname{diag}(\sin(\pi k/n))_{k=1}^{n-1}$. Put $A=2\widehat U^\dagger H\widehat U$. Then
--   $$\det A=1,\qquad T\bigl(A^{-1}(G/\eta)A^{-1}\bigr)=T(G/\eta).$$
--   This is the particular invariance the authors assert without proof. It is not invariance under arbitrary real matrices with determinant one.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 27, Appendix B, Eq. (B.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.27, Eq.(B.5): only the specifically constructed A is used.
The authors assert this equality without a proof; this is disclosed rather
than converted into a theorem hypothesis. -/
theorem special_theta_invariance (n : ℕ) (hn : 2 ≤ n) (eta x : ℝ)
    (heta : 0 < eta) (hx : 0 < x ∧ x < 1) :
    (specialA n).det = 1 ∧
    theta0 ((specialA n)⁻¹ * (eta⁻¹ • gammaMatrix n x) * (specialA n)⁻¹) =
      theta0 (eta⁻¹ • gammaMatrix n x) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
