-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_corollary2_independentDiscard
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.corollary2_independentDiscard
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:34:51.284972+00:00
-- url     : https://prove2.me/theorems/9821c636-91d7-4c14-8e00-a1d50c4b11da
-- title:
--   Corollary 2: discarding an independent tensor factor preserves cluster mutual information
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $1\le M<N$, let $T=\{M+1,\ldots,N\}$, and suppose the $N$-party state satisfies $\rho=\rho_{T^{\mathrm c}}\otimes\rho_T$, with both factors its actual marginals. Let $A,L$ be disjoint nonempty clusters such that $T\subseteq L$ and $L\setminus T$ is nonempty. For every subset $D\subseteq T$,
--
--   $$I(A:L)_\rho=I(A:L\setminus D)_\rho,$$
--
--   where $I(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{A\cup B})$. Each tensor block can itself be correlated. This allows removal of none or all of the independent tail.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 4, Corollary 2: discarding an independent tensor factor leaves cluster mutual information unchanged

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Corollary 2, PDF p.4: discarding any part of an independent tail preserves
cluster mutual information. The two tensor blocks need not factor internally. -/
theorem corollary2_independentDiscard {n M : ℕ} (hM : 1 ≤ M) (hMn : M < n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho)
    (hproduct : rho = productAcross rho (Finset.univ.filter (fun i => i.val < M)))
    (A L D : Cluster n) (hA : A.Nonempty) (hL : L.Nonempty)
    (hdisjoint : Disjoint A L)
    (htail : Finset.univ.filter (fun i : Fin n => M ≤ i.val) ⊆ L)
    (hretained : (L \ Finset.univ.filter (fun i : Fin n => M ≤ i.val)).Nonempty)
    (hD : D ⊆ Finset.univ.filter (fun i : Fin n => M ≤ i.val)) :
    clusterMutualInformation rho A L = clusterMutualInformation rho A (L \ D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
