-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_dual_period_transformation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.dual_period_transformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:29:44.131069+00:00
-- url     : https://prove2.me/theorems/8c06e426-491c-48ce-ace8-195984b2d15f
-- title:
--   Dual-period theta transformation
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Let $n\ge2$, $\eta>0$, and let $\widetilde G$ replace $\beta$ by its reciprocal in $G$. Then
--   $$T(\eta\widetilde G)=\eta^{-(n-1)/2}\left(\prod_{k=1}^{n-1}\beta_{k/n}(x)\right)^{1/2}T(G/\eta).$$
--   This relates the two period matrices while keeping the full dimensional power of $\eta$.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 27, Appendix B, Eq. (B.6); Eq. (59)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.27, Eq.(B.6), correcting the k=0 lower limit printed in (59)
on p.13 to k=1 as explicitly printed in (B.6). The exponent is -(n-1)/2. -/
theorem dual_period_transformation (n : ℕ) (hn : 2 ≤ n) (eta x : ℝ)
    (heta : 0 < eta) (hx : 0 < x ∧ x < 1) :
    theta0 (eta • dualGammaMatrix n x) =
      eta ^ (-((n - 1 : ℕ) : ℝ) / 2) * Real.sqrt (betaProduct n x) *
        theta0 (eta⁻¹ • gammaMatrix n x) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
