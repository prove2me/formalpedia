-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_small_x_replica_factor
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.small_x_replica_factor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:33:33.868822+00:00
-- url     : https://prove2.me/theorems/734ee5e9-92ad-49f7-a0aa-5d7148795236
-- title:
--   Leading small-cross-ratio term of the real replica quotient
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Fix $n\ge2$ and $\eta>0$, $\eta\ne1$, and set $\alpha=\min(\eta,\eta^{-1})$. Let $P_n(\alpha)=\sum_{\ell=1}^{n-1}(\ell/n)/\sin(\pi\ell/n)^{2\alpha}$. Then
--   $$\lim_{x\to0^+}\frac{Q_n(\eta,x)-1}{x^\alpha}=\sum_{\ell=1}^{n-1}\frac{2(n-\ell)}{[2n\sin(\pi\ell/n)]^{2\alpha}}=2n(4n^2)^{-\alpha}P_n(\alpha).$$
--   This is the real-field expansion; at $\eta=1$ the quotient is identically one, so this nonzero correction formula does not apply. The empty $n=1$ case is handled separately.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 15, Eqs. (72),(83)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.15, Eq.(72), and p.19, Eq.(83): leading small-x term of the
real-field quotient. Eta=1 is excluded because numerator and denominator
cancel there; the n=1 empty case is separately given in replica_symmetries. -/
theorem small_x_replica_factor (n : ℕ) (hn : 2 ≤ n) (eta : ℝ)
    (heta : 0 < eta) (hne : eta ≠ 1) :
    let alpha := min eta eta⁻¹
    Tendsto (fun x : ℝ => (replicaFactor n eta x - 1) / x ^ alpha)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (windingCoefficient n alpha)) ∧
    windingCoefficient n alpha =
      2 * (1 / (4 * (n : ℝ) ^ 2)) ^ alpha * (n : ℝ) * replicaP n alpha := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
