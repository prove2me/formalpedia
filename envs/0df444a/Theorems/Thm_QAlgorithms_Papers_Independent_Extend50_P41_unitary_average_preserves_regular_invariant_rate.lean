-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_unitary_average_preserves_regular_invariant_rate
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.unitary_average_preserves_regular_invariant_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:49:06.878554+00:00
-- url     : https://prove2.me/theorems/7d1bc896-694a-4d24-bfa8-3b373dd5c9e9
-- title:
--   Proposition 4.9: averaging preserves jointly lower semicontinuous invariant rates
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   Suppose a full scheme has rate $I$ which is jointly lower semicontinuous and invariant under simultaneous conjugation: $I(U\rho U^*,U\sigma U^*)=I(\rho,\sigma)$. Its normalized Haar average
--   $$\overline E_N(B)=\int U^{\otimes N}E_N(U^*BU)(U^*)^{\otimes N}\,dU$$
--   is a covariant normalized scheme satisfying the LDP with the same rate $I$, for every input including singular states. This constructs a covariant witness without assuming the original scheme is covariant.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 19, Proposition 4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.19-20, Proposition 4.9: joint LSC and simultaneous-conjugation
invariance of I suffice; covariance of the original scheme is not assumed. -/
theorem unitary_average_preserves_regular_invariant_rate {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (hregular : JointLSC I) (hinvariant : InvariantRate I) :
    ∃ A : Scheme d (DensityOutcome d),
      (∀ k B, MeasurableSet B → (A.observable k).operator B = unitaryAverageOperator E k B) ∧
      (∀ k, CovariantAt (A.observable k)) ∧ SchemeLDP A FullTarget I := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
