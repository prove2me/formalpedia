-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_pure_input_covariant_optimum
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.pure_input_covariant_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:56:45.519467+00:00
-- url     : https://prove2.me/theorems/fa29bd61-1250-414a-aba8-aa09ada693c4
-- title:
--   Proposition 5.5 / (33), (182), (184): exact covariant optimum for pure input
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Write $I_{\rm Id}$ for the pointwise supremum of all admissible full-estimation rates, $I_{\rm Id}^0$ for the supremum over jointly lower semicontinuous admissible rates, and $I_{\rm Id}^c$ for the supremum over rates admitting a covariant witnessing scheme. These suprema need not themselves be admissible. Let $\widehat I$ denote the principal-minor rate of (26), and write $S(\rho,\sigma)=D(\sigma\Vert\rho)$, with value infinity on support violations.
--
--   For every pure input $\rho$ and every estimate $\sigma$,
--   $$I_{\rm Id}^c(\rho,\sigma)=\widehat I(\rho,\sigma)=\begin{cases}-\log\operatorname{Tr}(\rho\sigma),&\sigma\text{ pure},\\+\infty,&\sigma\text{ not pure}.\end{cases}$$
--   The logarithmic value is infinity when the pure states are orthogonal. For non-pure $\sigma$, the regular and unrestricted optima also equal infinity. This determines the exact covariant optimum for pure inputs and includes the adjacent identities (182),(184).
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 34, Proposition 5.5 / (33),(182),(184),(199)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9,32,34, Proposition 5.5, (33),(182),(184),(199): exact covariant
optimum for pure input; non-pure estimates have infinite rate for every optimum.
No equality of mixed-input covariant and unrestricted optima is claimed. -/
theorem pure_input_covariant_optimum {d : ℕ} (hd : 0 < d)
    (rho : DensityOutcome d) (hpure : PureDensityState rho) (sigma : DensityOutcome d) :
    covariantOptimal rho sigma = fullRate rho sigma ∧
    (PureDensityState sigma → (fullRate rho sigma : EReal) =
      -logMass (ENNReal.ofReal (rho.val * sigma.val).trace.re)) ∧
    (¬ PureDensityState sigma → fullRate rho sigma = ⊤ ∧
      optimalRate FullTarget true rho sigma = ⊤ ∧
      optimalRate FullTarget false rho sigma = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
