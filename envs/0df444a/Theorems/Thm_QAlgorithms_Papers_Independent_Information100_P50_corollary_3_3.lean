-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_corollary_3_3
-- name    : QAlgorithms.Papers.Independent.Information100.P50.corollary_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:58:19.19922+00:00
-- url     : https://prove2.me/theorems/31ab61e4-e443-401a-af6a-dd0f3e5bd6bf
-- title:
--   Corollary 3.3: For every epsilon>0 and dim Y≥2, there exist four CP maps with common sum, diamond(Phi1-Phi2)=diamond(Psi1-Psi
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   Suppose $\dim Y\ge2$. For every $\varepsilon>0$, choose $0<\theta<\pi/2$ and unit vectors $a,b$ with $|\langle a,b\rangle|=\cos\theta$ and $\sin\theta<\varepsilon$. Such choices can be made so that the replacement channels $\Phi_1(X)=\operatorname{tr}(X)aa^*$, $\Psi_1(X)=\operatorname{tr}(X)bb^*$ and $\Phi_2=\Psi_2=(\Phi_1+\Psi_1)/2$ satisfy
--
--   $$\Phi_1+\Psi_1=\Phi_2+\Psi_2,\quad \|\Phi_1-\Phi_2\|_\diamond=\|\Psi_1-\Psi_2\|_\diamond=\sin\theta<\varepsilon,\quad \widehat F(\Phi_1,\Psi_1)=0,\quad\widehat F(\Phi_2,\Psi_2)=1.$$
--
--   Here $\widehat F$ is unsquared geometric channel fidelity. The common sum depends on the chosen angle. This is the source's explicit norm-close construction.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 11, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Corollary 3.3 and its replacement-map construction, source PDF p.11. The common
sum is chosen after epsilon, through the angle theta; it is not fixed in advance. -/
theorem corollary_3_3 {dx dy : ℕ} (hdx : 0 < dx) (hdy : 2 ≤ dy)
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
      cbTraceNorm (Phi1 - Phi2) = Real.sin theta ∧ cbTraceNorm (Phi1 - Phi2) < epsilon ∧
      geometricFidelity Phi1 Psi1 = 0 ∧ geometricFidelity Phi2 Phi2 = 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
