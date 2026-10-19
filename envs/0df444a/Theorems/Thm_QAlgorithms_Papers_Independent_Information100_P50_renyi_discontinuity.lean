-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_renyi_discontinuity
-- name    : QAlgorithms.Papers.Independent.Information100.P50.renyi_discontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:05:32.749726+00:00
-- url     : https://prove2.me/theorems/10f4fb4b-fd99-40f9-86e9-83385b41a473
-- title:
--   Unnumbered §5.1 discontinuity extension: For every 0<alpha<1, epsilon>0 and dimY≥2, the replacement-map splittings of Corollary 3
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For positive input dimension, $\dim Y\ge2$, $0<\alpha<1$, and every $\varepsilon>0$, there exist unit vectors $a,b$ of overlap $\cos\theta$, where $0<\theta<\pi/2$ and $\sin\theta<\varepsilon$, giving replacement channels $\Phi_1(X)=\operatorname{tr}(X)aa^*$, $\Psi_1(X)=\operatorname{tr}(X)bb^*$ and $\Phi_2=\Psi_2=(\Phi_1+\Psi_1)/2$ such that
--
--   $$\Phi_1+\Psi_1=\Phi_2+\Psi_2,\quad\|\Phi_1-\Phi_2\|_\diamond=\|\Psi_1-\Psi_2\|_\diamond<\varepsilon,\quad \widehat Q_\alpha(\Phi_1\|\Psi_1)=0,\quad\widehat Q_\alpha(\Phi_2\|\Psi_2)=1.$$
--
--   The quasi-entropy is the common-input output infimum of $\operatorname{tr}(B\#_\alpha A)$. This pins the prose extension to its explicit construction and exact values.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 18, Unnumbered §5.1 discontinuity extension

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Unnumbered Section 5.1 extension of Proposition 3.2, source PDF p.18; the same
replacement channels give exact values 0 and 1 even at arbitrarily small norm distance. -/
theorem renyi_discontinuity {dx dy : ℕ} (hdx : 0 < dx) (hdy : 2 ≤ dy)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (theta : ℝ) (a b : EuclideanSpace ℂ (Fin dy)),
      0 < theta ∧ theta < Real.pi / 2 ∧ Real.sin theta < epsilon ∧
      IsState a ∧ IsState b ∧ ‖inner ℂ a b‖ = Real.cos theta ∧
      let Phi1 : Lin dx dy := replacementMap a
      let Psi1 : Lin dx dy := replacementMap b
      let Phi2 : Lin dx dy := replacementAverage a b
      IsChannel Phi1 ∧ IsChannel Psi1 ∧ IsChannel Phi2 ∧
      Phi1 + Psi1 = Phi2 + Phi2 ∧
      cbTraceNorm (Phi1 - Phi2) = cbTraceNorm (Psi1 - Phi2) ∧
      cbTraceNorm (Phi1 - Phi2) < epsilon ∧
      renyiQ alpha Phi1 Psi1 = 0 ∧ renyiQ alpha Phi2 Phi2 = 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
