-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_permutationInvariantSufficient
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.permutationInvariantSufficient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:36:14.639232+00:00
-- url     : https://prove2.me/theorems/c5880c41-d164-4cbc-9232-a6f488d03002
-- title:
--   Permutation averaging preserves all identical product states
-- statement:
--   Let $M=B(H)$ be a nonzero finite-dimensional matrix algebra, let $n\geq1$, and let $\{\rho_\theta:\theta\in\Theta\}$ be any family of density matrices, without a faithfulness assumption. Let $U_\pi$ permute the $n$ tensor factors, and define the family-independent map
--
--   $$\mathcal E(A)=\frac1{n!}\sum_{\pi\in S_n}U_\pi A U_\pi^*.$$
--
--   This is a normal unital $2$-positive map whose values lie in the permutation-invariant algebra, and
--
--   $$\operatorname{Tr}(\rho_\theta^{\otimes n}\mathcal E(A))=\operatorname{Tr}(\rho_\theta^{\otimes n}A)\qquad(\theta\in\Theta,\ A\in M^{\otimes n}).$$
--
--   Consequently, the permutation-invariant subalgebra is sufficient for the identical product-state experiment. The common map is constructed before any parameter is considered.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 12, Example 6: permutation-invariant subalgebra is sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- Example 6, PDF p.12: the permutation-invariant subalgebra is sufficient
for every family of n-fold identical product states, including nonfaithful
states. The constructed normal coarse-graining maps into that algebra and
preserves every family expectation. In finite dimension normality is automatic. -/
theorem permutationInvariantSufficient
    {I Theta : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (n : ℕ) (hn : 1 ≤ n)
    (rho : Theta → Matrix I I ℂ)
    (hRho : ∀ theta, QAlgorithms.IsDensityMatrix (rho theta)) :
    IsCStarCoarseGraining (permutationAverage (I := I) n) ∧
    (∀ (A : Matrix (Fin n → I) (Fin n → I) ℂ)
      (p : Equiv.Perm (Fin n)) (x y : Fin n → I),
      permutationAverage n A (x ∘ p) (y ∘ p) = permutationAverage n A x y) ∧
    (∀ theta (A : Matrix (Fin n → I) (Fin n → I) ℂ),
      (copies n (rho theta) * permutationAverage n A).trace =
        (copies n (rho theta) * A).trace) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
