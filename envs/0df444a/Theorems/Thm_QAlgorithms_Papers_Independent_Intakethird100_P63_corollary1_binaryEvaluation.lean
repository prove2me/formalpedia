-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_corollary1_binaryEvaluation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.corollary1_binaryEvaluation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:34:10.953625+00:00
-- url     : https://prove2.me/theorems/0bf0edd8-c786-4aee-96cc-cf57174b1fe9
-- title:
--   Corollary 1: evaluation along every successive binary partition
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $N\ge2$ and let $\rho$ be an $N$-party state. Consider any finite full binary partition tree whose root is the full party set, whose children are disjoint nonempty clusters partitioning their parent, and whose leaves are the singleton parties. If $L_v,R_v$ are the two child clusters of internal node $v$, define $I(A:B)=S_A+S_B-S_{A\cup B}$ using the actual marginals. Then
--
--   $$I_{\{1,\ldots,N\}}=\sum_{v\text{ internal}} I(L_v:R_v).$$
--
--   The result evaluates total correlation using arbitrary successive binary choices, including the final split into two singletons.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 3, Corollary 1: evaluation by arbitrary successive binary partitions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Corollary 1, PDF p.3: every valid full binary partition tree evaluates the same
total correlation, retaining all within-cluster terms until the singleton leaves. -/
theorem corollary1_binaryEvaluation {n : ℕ} (hn : 2 ≤ n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho)
    (t : BinaryTree n) (ht : t.Valid) (hroot : t.parties = Finset.univ) :
    clusterInformation rho Finset.univ = t.information rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
