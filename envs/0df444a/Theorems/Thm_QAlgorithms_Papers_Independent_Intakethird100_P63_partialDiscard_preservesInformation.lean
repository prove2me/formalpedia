-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_partialDiscard_preservesInformation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.partialDiscard_preservesInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:42:10.044218+00:00
-- url     : https://prove2.me/theorems/d3cf0e9a-d493-4f28-9865-02d49663de2d
-- title:
--   Closing result: partial discarding inside the third cluster preserves mutual information
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension. A discrete ensemble may have finitely or countably many components: its weights $w_k$ are nonnegative and sum to one, and each component with $w_k>0$ is a normalized density operator. Every mixture below is the computed trace-norm convergent sum $\rho=\sum_k w_k\rho^k$. All component conditions concern positive-weight labels only.
--
--   Let $A,B,R$ be nonempty pairwise disjoint clusters partitioning a finite party set. Suppose the component reductions on $A$ and $B$ are biorthogonal across distinct active labels, and every active component satisfies $I(A:B)_{\rho^k}=I(A:BR)_{\rho^k}$. For every subset $D\subseteq R$,
--
--   $$I(A:BR)_\rho=I(A:B(R\setminus D))_\rho=I(A:B)_\rho,$$
--
--   where juxtaposition denotes union of disjoint clusters and $I(X:Y)=S_X+S_Y-S_{X\cup Y}$. The clusters $A,B$ may themselves be composite. This includes retaining all of $R$ and discarding all of it.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 8, Unnumbered closing result: partial discarding inside the third cluster also preserves mutual information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Closing unnumbered result, PDF p.8: in the Theorem 2 family, every intermediate
discard inside the third cluster preserves mutual information. The endpoint parties
may themselves be composite clusters. Empty D and D=R are included. -/
theorem partialDiscard_preservesInformation {n : ℕ}
    (e : DiscreteDensityEnsemble (Fin n → ℕ)) (A B R : Cluster n)
    (hA : A.Nonempty) (hB : B.Nonempty) (hR : R.Nonempty)
    (hAB : Disjoint A B) (hAR : Disjoint A R) (hBR : Disjoint B R)
    (hcover : A ∪ B ∪ R = Finset.univ)
    (hbio : Biorthogonal e A B)
    (hfinite : FiniteSubsystemEntropies (herbutMixture e))
    (hssa : ∀ k, 0 < e.weight k →
      clusterMutualInformation (e.component k) A B = clusterMutualInformation (e.component k) A (B ∪ R))
    (D : Cluster n) (hD : D ⊆ R) :
    clusterMutualInformation (herbutMixture e) A (B ∪ R) = clusterMutualInformation (herbutMixture e) A (B ∪ (R \ D)) ∧
    clusterMutualInformation (herbutMixture e) A (B ∪ (R \ D)) = clusterMutualInformation (herbutMixture e) A B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
