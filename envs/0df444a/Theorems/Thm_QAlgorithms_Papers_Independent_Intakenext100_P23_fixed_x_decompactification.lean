-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_fixed_x_decompactification
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.fixed_x_decompactification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:31:48.079105+00:00
-- url     : https://prove2.me/theorems/0af6ea9c-dae8-4aa0-8590-049acef784f2
-- title:
--   Fixed-cross-ratio decompactification of the complex expression
-- statement:
--   For a positive integer $n$ and $0<x<1$, let $F_y(x)={}_2F_1(y,1-y;1;x)$ and $\beta_y(x)=F_y(1-x)/F_y(x)$. Write $G=-i\Gamma$, where
--   $$G_{rs}=\frac{2}{n}\sum_{k=1}^{n-1}\sin(\pi k/n)\beta_{k/n}(x)\cos(2\pi k(r-s)/n),\qquad 1\le r,s<n.$$
--   For a real positive definite matrix $H$, write $T(H)=\sum_{m\in\mathbb Z^{n-1}}e^{-\pi m^{\mathsf T}Hm}=\Theta(0\mid iH)$, and put $Q_n(\eta,x)=T(\eta G)T(G/\eta)/T(G)^2$. Empty matrices and products at $n=1$ have theta value and product equal to one.
--
--   Fix $n\ge1$ and $x\in(0,1)$. Let $J_n(x)=\prod_{k=1}^{n-1}F_{k/n}(x)$. As $\eta\to\infty$,
--   $$T(\eta G)\to1,\qquad \frac{\sqrt{\det G}\,T(G/\eta)}{\eta^{(n-1)/2}}\to1,\qquad \frac{Q_n(\eta,x)^2J_n(x)J_n(1-x)}{\eta^{n-1}}\to1.$$
--   The dual limit is $Q_n(\eta,x)^2J_n(x)J_n(1-x)\eta^{n-1}\to1$ as $\eta\to0^+$. These are leading asymptotics for the explicit complex-field expression, with $n,x$ fixed, not finite-radius equalities or estimates uniform near contact.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 14, Section 4.4, Eqs. (65)–(66)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.14, (65)--(66): fixed n,x decompactification of the explicit
complex-field expression. These are ratio asymptotics, not exact equalities
at finite eta; no uniformity in x near the endpoints is claimed. -/
theorem fixed_x_decompactification (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : 0 < x ∧ x < 1) :
    Tendsto (fun eta : ℝ => theta0 (eta • gammaMatrix n x)) atTop (𝓝 1) ∧
    Tendsto (fun eta : ℝ => theta0 (eta⁻¹ • gammaMatrix n x) *
      Real.sqrt (gammaMatrix n x).det / eta ^ (((n - 1 : ℕ) : ℝ) / 2)) atTop (𝓝 1) ∧
    Tendsto (fun eta : ℝ => replicaFactor n eta x ^ 2 *
      (hypergeometricProduct n x * hypergeometricProduct n (1 - x)) /
        eta ^ (n - 1)) atTop (𝓝 1) ∧
    Tendsto (fun eta : ℝ => replicaFactor n eta x ^ 2 *
      (hypergeometricProduct n x * hypergeometricProduct n (1 - x)) *
        eta ^ (n - 1)) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
