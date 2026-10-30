-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_pure_local_symmetric_tests
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.pure_local_symmetric_tests
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:56:12.547289+00:00
-- url     : https://prove2.me/theorems/19a3293f-cb37-466b-b4d7-65789a2211f2
-- title:
--   Lemma 5.4: pure-state local tests reduced to symmetric unit vectors
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Let $I$ be admissible for full estimation, and let $\rho=|\phi\rangle\langle\phi|$, $\sigma=|\psi\rangle\langle\psi|$ with $\|\phi\|=\|\psi\|=1$. There are unit vectors $\Psi_N$ in the symmetric subspace of $(\mathbb C^d)^{\otimes N}$ such that
--   $$\liminf_N-\frac1N\log|\langle\phi^{\otimes N},\Psi_N\rangle|^2\ge I(\rho,\sigma),\qquad |\langle\Psi_N,\psi^{\otimes N}\rangle|^2\longrightarrow1.$$
--   If $I$ has a covariant witnessing scheme, the sequence can be chosen as $\Psi_N=\psi^{\otimes N}$ for every $N$. This reduces local pure-state tests to normalized symmetric vectors without confusing rate invariance with covariance of a witness.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 33, Lemma 5.4 / (185),(186)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.33-34, Lemma 5.4, (185)-(186): normalized symmetric tests, and the
special tensor-vector choice when I has a covariant witnessing scheme. -/
theorem pure_local_symmetric_tests {d : ℕ} (hd : 0 < d)
    (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞) (hI : AdmissibleRate FullTarget I)
    (rho sigma : DensityOutcome d) (phi psi : EuclideanSpace ℂ (Fin d))
    (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (hrho : rho.val = pureDensity phi) (hsigma : sigma.val = pureDensity psi) :
    ∃ v : (k : ℕ) → EuclideanSpace ℂ (CopyIndex d k),
      PureTestProperties I rho sigma phi psi v ∧
      (CovariantAdmissible I → ∀ k, v k = tensorPow (k+1) psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
