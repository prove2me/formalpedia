-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_corollary_5_14
-- name    : QAlgorithms.Papers.Independent.Information100.P50.corollary_5_14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:08:39.279051+00:00
-- url     : https://prove2.me/theorems/134efd8a-3e71-4948-8229-2afe0f767c62
-- title:
--   Corollary 5.14: For bounded endpoint operator-convex f with f(1)=0 and CP Phi,Psi with range(J(Phi)) intersection range(J(Psi)
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   Let $f:(0,\infty)\to\mathbb R$ be operator convex in every matrix size, with $f(1)=0$ and finite real limits $a=f(0+)$ and $b=\lim_{t\to\infty}f(t)/t$. The maximal divergence $\widehat D_f$ is defined independently by the regularized state perspective and a supremum over a common bipartite density input. Outputs are not required to have trace one.
--
--   For CP maps with $\operatorname{range}(J(\Phi))\cap\operatorname{range}(J(\Psi))=\{0\}$,
--
--   $$\widehat D_f(\Phi\|\Psi)=\lambda_{\max}\!\left(a\Psi^*(I_Y)+b\Phi^*(I_Y)\right).$$
--
--   If $\dim Y\ge2$, then for every $\varepsilon>0$ the unit-vector replacement construction of Corollary 3.3 gives $\Phi_1(X)=\operatorname{tr}(X)uu^*$, $\Psi_1(X)=\operatorname{tr}(X)vv^*$ and $\Phi_2=\Psi_2=(\Phi_1+\Psi_1)/2$, with $|\langle u,v\rangle|=\cos\theta$, $0<\theta<\pi/2$, $\sin\theta<\varepsilon$, and
--
--   $$\|\Phi_1-\Phi_2\|_\diamond=\|\Psi_1-\Psi_2\|_\diamond<\varepsilon,\quad \widehat D_f(\Phi_1\|\Psi_1)=a+b,\quad\widehat D_f(\Phi_2\|\Psi_2)=0.$$
--
--   These are existentially constructed channels with one common sum. The jump $a+b$ may be zero for an affine generator.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 23, Corollary 5.14

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Corollary 5.14, source PDF pp.23–24. The special pairs are the actual replacement
construction, and the quantitative jump may be zero for affine f. -/
theorem corollary_5_14 {dx dy : ℕ} (hdx : 0 < dx) (hdy : 0 < dy) (f : BoundedGenerator) :
    (∀ Phi Psi : Lin dx dy, Entanglement.IsCompletelyPositive Phi →
      Entanglement.IsCompletelyPositive Psi →
      matrixRange (choiMatrix Phi) ⊓ matrixRange (choiMatrix Psi) = ⊥ →
      channelDivergence f.f Phi Psi = maxEigenvalue
        ((atZero f.f : ℂ) • hilbertSchmidtAdjoint Psi 1 +
          (atInfinity f.f : ℂ) • hilbertSchmidtAdjoint Phi 1)) ∧
    (2 ≤ dy → ∀ epsilon : ℝ, 0 < epsilon →
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
        channelDivergence f.f Phi1 Psi1 = atZero f.f + atInfinity f.f ∧
        channelDivergence f.f Phi2 Phi2 = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
