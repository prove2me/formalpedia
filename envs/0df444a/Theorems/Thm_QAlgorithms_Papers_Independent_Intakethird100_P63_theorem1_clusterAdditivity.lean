-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_theorem1_clusterAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.theorem1_clusterAdditivity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T08:33:28.759446+00:00
-- url     : https://prove2.me/theorems/d50623e0-7e37-4dbb-a479-a6552011f69c
-- title:
--   Theorem 1: correlation information is additive over every cluster partition
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $N\ge1$, let $\rho$ be an $N$-party state, and let $\Pi$ be any partition of its parties into nonempty clusters $C$. Write $S_C=S(\rho_C)$ for the entropy of its computed cluster marginal, $I_C=\sum_{n\in C}S_{\{n\}}-S_C$, and $I_\Pi=\sum_{C\in\Pi}S_C-S_{\{1,\ldots,N\}}$. Then
--
--   $$I_{\{1,\ldots,N\}}=I_\Pi+\sum_{C\in\Pi}I_C.$$
--
--   This separates correlations among clusters from correlations within them. Singleton clusters have zero internal correlation, and the one-cluster partition is included.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 3, Theorem 1: additivity of correlation information for every cluster partition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Theorem 1, PDF pp.2–3, (6): every cluster partition is allowed, including the
one-block partition and all-singleton partition. -/
theorem theorem1_clusterAdditivity {n : ℕ} (hn : 1 ≤ n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho)
    (P : Finset (Cluster n)) (hP : IsPartition P) :
    clusterInformation rho Finset.univ = amongCorrelation rho P + ∑ C ∈ P, clusterInformation rho C := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
