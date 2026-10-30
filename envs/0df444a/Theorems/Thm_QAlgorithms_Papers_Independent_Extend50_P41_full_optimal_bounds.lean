-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_full_optimal_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.full_optimal_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:39:58.909453+00:00
-- url     : https://prove2.me/theorems/426b6903-374a-4807-9013-ca258a35bce7
-- title:
--   Equation (31): bounds for optimal full-estimation rate functions
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Write $I_{\rm Id}$ for the pointwise supremum of all admissible full-estimation rates, $I_{\rm Id}^0$ for the supremum over jointly lower semicontinuous admissible rates, and $I_{\rm Id}^c$ for the supremum over rates admitting a covariant witnessing scheme. These suprema need not themselves be admissible. Let $\widehat I$ denote the principal-minor rate of (26), and write $S(\rho,\sigma)=D(\sigma\Vert\rho)$, with value infinity on support violations.
--
--   For every pair of states,
--   $$\widehat I\le I_{\rm Id}^c\le I_{\rm Id}\le S,\qquad \widehat I\le I_{\rm Id}^0\le I_{\rm Id}\le S.$$
--   All inequalities are pointwise. The display gives two branches and compares neither restricted optimum to the other. It records the established bounds without promoting the subsequent conjectures to theorems.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 9, Equation (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, (31): two branches. There is no claimed comparison between the
covariant and regular suprema. -/
theorem full_optimal_bounds {d : ℕ} (hd : 0 < d) (rho sigma : DensityOutcome d) :
    fullRate rho sigma ≤ covariantOptimal rho sigma ∧
    fullRate rho sigma ≤ optimalRate FullTarget true rho sigma ∧
    covariantOptimal rho sigma ≤ optimalRate FullTarget false rho sigma ∧
    optimalRate FullTarget true rho sigma ≤ optimalRate FullTarget false rho sigma ∧
    optimalRate FullTarget false rho sigma ≤ QuantumLoss.umegakiEntropy sigma.val rho.val sigma.property rho.property := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
