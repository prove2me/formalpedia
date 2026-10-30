-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_admissible_rate_entropy_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.admissible_rate_entropy_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:37:33.288586+00:00
-- url     : https://prove2.me/theorems/e7170667-707b-4e71-9d16-3379550f28d7
-- title:
--   Theorem 3.3: universal quantum-relative-entropy upper bound
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For every admissible full-estimation rate $I$ and all states $\rho,\sigma$,
--   $$I(\rho,\sigma)\le S(\rho,\sigma)=D(\sigma\Vert\rho).$$
--   When finite, the right side is $\operatorname{Tr}[\sigma(\log\sigma-\log\rho)]$; otherwise it is infinity. This gives a universal exponent bound over all schemes.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 8, Theorem 3.3 / (27)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Theorem 3.3, (27): the orientation is D(sigma||rho), with infinity
on support violations. No full-rank assumption is imposed. -/
theorem admissible_rate_entropy_bound {d : ℕ} (hd : 0 < d)
    (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞) (hI : AdmissibleRate FullTarget I) :
    ∀ rho sigma, I rho sigma ≤ QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
