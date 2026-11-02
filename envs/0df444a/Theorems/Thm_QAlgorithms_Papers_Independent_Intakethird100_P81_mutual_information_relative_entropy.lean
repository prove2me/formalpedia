-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_mutual_information_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.mutual_information_relative_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:58:05.987073+00:00
-- url     : https://prove2.me/theorems/6cde6c5b-e0c8-489f-b6cc-c2768d2374ac
-- title:
--   Mutual information as relative entropy and its sharp bound
-- statement:
--   Let $\rho_{AB}$ be a normalized density matrix of a finite bipartite complex system. Compute both marginals from this same state: $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and $\rho_B=\operatorname{Tr}_A\rho_{AB}$. Define $S(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$, with entropy measured in bits. Then the product of the marginals is a density matrix and
--   $$
--   S(A:B)=S_2(\rho_{AB}\Vert\rho_A\otimes\rho_B)
--   \ge\frac{\|\rho_{AB}-\rho_A\otimes\rho_B\|_1^2}{2\ln 2}.
--   $$
--
--   The identity and bound relate correlations to the full trace-norm distance from independence. The product state is constructed from the joint state, including when marginals are singular.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 11, Unnumbered display following Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Unnumbered display, PDF p.11: both the relative-entropy identity and its sharp lower bound.
The product matrix and its normalization are conclusions constructed from rho. -/
theorem mutual_information_relative_entropy {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ hprod : IsDensityMatrix (jointMarginalProduct rho),
      relativeEntropyBits rho (jointMarginalProduct rho) =
        ENNReal.ofReal (jointMutualInfoBits rho) ∧
      (traceNorm (rho - jointMarginalProduct rho)) ^ 2 / (2 * Real.log 2) ≤
        jointMutualInfoBits rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
