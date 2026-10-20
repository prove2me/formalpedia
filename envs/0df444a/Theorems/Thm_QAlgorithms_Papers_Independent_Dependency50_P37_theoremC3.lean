-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC3
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:22:54.693277+00:00
-- url     : https://prove2.me/theorems/6de52679-4697-4d31-a3ed-e4cac49d58aa
-- title:
--   Mixing via least invariant support and left Kraus-word spans
-- statement:
--   Let $d\ge1$ and let $K_1,\ldots,K_p\in M_d(\mathbb C)$ satisfy $\sum_iK_i^*K_i=I$. Put $\Phi(X)=\sum_iK_iXK_i^*$. Let $\mathcal K_n=\operatorname{span}\{K_{i_1}\cdots K_{i_n}\}$. A least nonzero invariant subspace $S$ is itself nonzero and invariant and is contained in every nonzero invariant subspace. If $P$ denotes its orthogonal projector, the following are equivalent:
--
--   $$
--   \begin{aligned}
--   &\Phi\text{ is mixing};\\
--   &\exists S,P\ \exists N\in\mathbb N_{\ge1}:\ \operatorname{supp}(P\Phi^n(\rho)P)=S
--      \text{ for every density }\rho\text{ and all }n\ge N;\\
--   &\exists S,P\ \exists N\in\mathbb N_{\ge1}:\ P\mathcal K_n=PM_d(\mathbb C)\text{ for all }n\ge N.
--   \end{aligned}
--   $$
--
--   In each existential clause, $S$ and $P$ have the properties just specified; only $N$ is an integer. This characterizes mixing using eventual saturation inside its invariant support.
--
--   **Formalization Note** C.1 is interpreted as quantifying over nonzero invariant comparison subspaces, consistently with the proof. Left multiplication is not replaced by two-sided compression.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 21, Theorem C.3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Theorem C.3, PDF pp.21–23. C.1 is interpreted with NONZERO invariant
comparison subspaces, as required by its proof. P is exactly the orthogonal
projector onto the least nonzero invariant subspace, not free compression data. -/
theorem theoremC3 {d p : ℕ} (hd : 0 < d) (K : Fin p → Operator d)
    (hK : IsKrausFamily K) :
    (Mixing (krausApply K) ↔
      ∃ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), ∃ P : Operator d,
        LeastInvariantSubspace (krausApply K) S ∧ OrthogonalProjectorOnto P S ∧
        ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ rho : Operator d,
          IsDensityMatrix rho → operatorRange (P * Nat.iterate (krausApply K) n rho * P) = S) ∧
    (Mixing (krausApply K) ↔
      ∃ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), ∃ P : Operator d,
        LeastInvariantSubspace (krausApply K) S ∧ OrthogonalProjectorOnto P S ∧
        ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
          leftMultiplySpace P (krausWordSpace K n) = leftMultiplySpace P ⊤) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
