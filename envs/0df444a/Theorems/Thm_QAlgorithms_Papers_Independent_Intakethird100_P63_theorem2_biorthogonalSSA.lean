-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_theorem2_biorthogonalSSA
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.theorem2_biorthogonalSSA
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:35:38.981542+00:00
-- url     : https://prove2.me/theorems/0be6adc2-98c0-49c0-97f8-1a6507e98597
-- title:
--   Theorem 2: biorthogonal mixtures preserve SSA equality and yield correlated nonproduct cases
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension. A discrete ensemble may have finitely or countably many components: its weights $w_k$ are nonnegative and sum to one, and each component with $w_k>0$ is a normalized density operator. Every mixture below is the computed trace-norm convergent sum $\rho=\sum_k w_k\rho^k$. All component conditions concern positive-weight labels only.
--
--   For a tripartite ensemble suppose that for distinct active labels $k,l$, both $\rho_1^k\rho_1^l=0$ and $\rho_2^k\rho_2^l=0$. If every active component satisfies $I(1:2)_{\rho^k}=I(1:23)_{\rho^k}$, then
--
--   $$I(1:2)_\rho=I(1:23)_\rho.$$
--
--   Moreover, if at least two labels have positive weight and $\rho\ne\rho_{12}\otimes\rho_3$, then
--
--   $$I(2:3)_\rho>0.$$
--
--   Here $I(A:B)=S_A+S_B-S_{A\cup B}$ and all subscripts denote actual marginals. The result gives SSA equality beyond independent-third-factor states.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 5, Theorem 2 (seed paper result): biorthogonal mixtures preserve SSA equality, with correlated nonproduct cases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Theorem 2, PDF pp.5,7: both SSA equality and positivity outside the aggregate
product exception (8). Finiteness of mixture marginals implies it for active components.
Zero labels do not count toward the condition of at least two terms. -/
theorem theorem2_biorthogonalSSA (e : DiscreteDensityEnsemble (Fin 3 → ℕ))
    (hbio : Biorthogonal e {0} {1})
    (hfinite : FiniteSubsystemEntropies (herbutMixture e))
    (hssa : ∀ k, 0 < e.weight k →
      clusterMutualInformation (e.component k) {0} {1} = clusterMutualInformation (e.component k) {0} {1, 2}) :
    clusterMutualInformation (herbutMixture e) {0} {1} = clusterMutualInformation (herbutMixture e) {0} {1, 2} ∧
    ((∃ k l, k ≠ l ∧ 0 < e.weight k ∧ 0 < e.weight l) →
      herbutMixture e ≠ productAcross (herbutMixture e) {0, 1} →
      0 < clusterMutualInformation (herbutMixture e) {1} {2}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
