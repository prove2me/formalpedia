-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P63_lemma1_subadditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P63.lemma1_subadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:32:44.728379+00:00
-- url     : https://prove2.me/theorems/a33f1eff-109e-45a4-8f7c-b29dd452f297
-- title:
--   Lemma 1: multipartite subadditivity and its equality case
-- statement:
--   All states below are positive trace-class density operators of trace one on completed complex Hilbert tensor products, represented in countable orthonormal coordinates. Finite dimensional systems are included. Entropies use natural logarithms and the convention $0\log 0=0$. Every subsystem entropy occurring in an entropy difference is finite; this is the proof-supported finite-entropy reading of the source, and imposes no finite Hilbert dimension.
--
--   Let $N\ge2$, let $\rho$ be an $N$-party state, and let $\rho_n$ be its actual marginal on party $n$. Then
--
--   $$S(\rho)\le\sum_{n=1}^{N}S(\rho_n),\qquad S(\rho)=\sum_{n=1}^{N}S(\rho_n)\iff\rho=\bigotimes_{n=1}^{N}\rho_n.$$
--
--   Thus equality characterizes complete absence of correlations among the parties.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, PDF p. 2, Lemma 1: multipartite subadditivity and its equality case

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- Lemma 1, PDF p.2, (1): multipartite subadditivity and its full equality case.
Finite subsystem entropies make the source's equality characterization meaningful. -/
theorem lemma1_subadditivity {n : ℕ} (hn : 2 ≤ n)
    (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (hrho : IsDensity rho)
    (hfinite : FiniteSubsystemEntropies rho) :
    herbutMarginalEntropy rho Finset.univ ≤ ∑ i : Fin n, herbutMarginalEntropy rho {i} ∧
    (herbutMarginalEntropy rho Finset.univ = ∑ i : Fin n, herbutMarginalEntropy rho {i} ↔
      rho = tensorMarginals rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P63

end
