-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_optimal_rates_invariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.optimal_rates_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:49:47.03524+00:00
-- url     : https://prove2.me/theorems/3e819031-b055-4ffa-b4e1-c90800f77588
-- title:
--   Proposition 4.10: invariance of the unrestricted and regular optimal rate functions
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Write $I_{\rm Id}$ for the pointwise supremum of all admissible full-estimation rates, $I_{\rm Id}^0$ for the supremum over jointly lower semicontinuous admissible rates, and $I_{\rm Id}^c$ for the supremum over rates admitting a covariant witnessing scheme. These suprema need not themselves be admissible. Let $\widehat I$ denote the principal-minor rate of (26), and write $S(\rho,\sigma)=D(\sigma\Vert\rho)$, with value infinity on support violations.
--
--   For all unitaries $U$ and all states $\rho,\sigma$,
--   $$I_{\rm Id}(U\rho U^*,U\sigma U^*)=I_{\rm Id}(\rho,\sigma),\qquad I_{\rm Id}^0(U\rho U^*,U\sigma U^*)=I_{\rm Id}^0(\rho,\sigma).$$
--   This is invariance of both pointwise optima on the entire state space. The two conjugations have the same orientation, as in (11) and the proof.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 20, Proposition 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.20, Proposition 4.10: both optimal rates are invariant under the
same conjugation in both arguments, as specified in (11) and used in the proof. -/
theorem optimal_rates_invariant {d : ℕ} (hd : 0 < d) :
    InvariantRate (optimalRate (FullTarget (d := d)) false) ∧
    InvariantRate (optimalRate (FullTarget (d := d)) true) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
