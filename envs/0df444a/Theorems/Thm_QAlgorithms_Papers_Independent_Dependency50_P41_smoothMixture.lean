-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_smoothMixture
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.smoothMixture
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:56:11.629173+00:00
-- url     : https://prove2.me/theorems/a13a5e69-3b7e-4f49-82b5-55f503c5cd2c
-- title:
--   Smooth conditional log-rank bound for normalized mixtures
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Fix orthonormal classical labels $|k\rangle_B$. Let $N\ge1$, $p_j>0$, $\sum_jp_j=1$, and let $\rho^j_{AB}=\sum_k\rho_A^{j,k}\otimes|k\rangle\langle k|$ be normalized states with positive A-blocks. Put $\rho=\sum_jp_j\rho^j$. For $\varepsilon\ge0$, define $H_0^\varepsilon(A|B)_\tau$ as the infimum of the extended conditional log-rank entropy over positive operators in this fixed classical basis whose full trace-norm distance from $\tau$ is at most $\varepsilon$, without a trace restriction on smoothing operators. Then $$H_0^\varepsilon(A|B)_\rho\le\max_{1\le j\le N}H_0^\varepsilon(A|B)_{\rho^j}+\log_2N.$$
--
--   This is the mixture estimate for trace-norm smoothing. The infimum corrects the printed supremum in Definition 4, as required by the proof.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 20, Lemma 27

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF p.20, Lemma 27, (A5).
Mixtures are normalized as used in the proof. Definition 4's sup is corrected to inf;
the printed type P(H_AB) of the A-blocks is corrected to P(H_A). -/
theorem smoothMixture {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : ℕ) (hN : 0 < N) (p : Fin N → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : Fin N → K → Op A) (hblocks : ∀ j k, (blocks j k).PosSemidef)
    (hstates : ∀ j, IsDensityMatrix (cqOperator v (blocks j)))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    smoothH0 (∑ j, (p j : ℂ) • cqOperator v (blocks j)) v epsilon ≤
      (⨆ j, smoothH0 (cqOperator v (blocks j)) v epsilon) +
        (Real.logb 2 (N : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
