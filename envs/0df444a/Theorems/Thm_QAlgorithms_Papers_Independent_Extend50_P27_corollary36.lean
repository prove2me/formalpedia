-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary36
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary36
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:59:54.838128+00:00
-- url     : https://prove2.me/theorems/45ce39a9-4f8c-493e-96d0-c09a417b537d
-- title:
--   Corollary 36: inverse-square-root coefficients recover fixed-resource fidelity
-- statement:
--   Use $N\ge1$, $d\ge2$, physical diagrams $\alpha\vdash N-1$, $\mu\vdash N$, and one-box compatibility $\mu\in\alpha$. Let $d_\lambda$ and $m_\lambda$ be the actual Specht dimensions and tensor-permutation multiplicities. The operators $F_\mu(\alpha)$ are constructed by Eq. (145), and $\lambda_\mu(\alpha)=N m_\mu d_\alpha/(d^N m_\alpha d_\mu)>0$. All sums below use compatible physical labels. Write $\rho_\alpha^t=\sum_{\mu\in\alpha}\lambda_\mu(\alpha)^tF_\mu(\alpha)$, extended by zero off its support.
--
--   On every compatible pair set
--
--   $$p_\mu(\alpha)=\lambda_\mu(\alpha)^{-1/2}=\sqrt{\frac{d^Nm_\alpha d_\mu}{N d_\alpha m_\mu}}.$$
--
--   In the scalar expression before maximization in Eq. (68), these coefficients give
--
--   $$\frac{N}{d^{2N+2}}\sum_\alpha\frac{d_\alpha}{m_\alpha}\left(\sum_{\mu\in\alpha}p_\mu(\alpha)m_\mu\right)^2
--   =\frac1{d^{N+2}}\sum_\alpha\left(\sum_{\mu\in\alpha}\sqrt{d_\mu m_\mu}\right)^2.$$
--
--   This identifies fixed-EPR-resource fidelity and does not claim joint resource optimality.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 26, Corollary 36: inverse-square-root coefficients recover fixed-resource fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Corollary 36, Eq.(121): inverse-square-root coefficients recover Eq.(120)
from the scalar expression (68), rather than the jointly optimized resource value
(PDF p.26). -/
theorem corollary36 {d K : ℕ} (hd : 2 ≤ d) :
    (∀ (alpha : Partition d K) (mu : Partition d (K+1)), Predecessor alpha.val mu.val →
      (Real.sqrt (lambdaValue alpha mu))⁻¹ =
        Real.sqrt ((d : ℝ)^(K+1) * tensorMultiplicity alpha * irrepDim mu /
          ((K+1 : ℝ) * irrepDim alpha * tensorMultiplicity mu))) ∧
    coefficientFidelity (fun (alpha : Partition d K) (mu : Partition d (K+1)) =>
      (Real.sqrt (lambdaValue alpha mu))⁻¹) = eprFormula d K := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
