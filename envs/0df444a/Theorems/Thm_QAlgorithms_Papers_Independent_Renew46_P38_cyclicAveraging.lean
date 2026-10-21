-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_cyclicAveraging
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.cyclicAveraging
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:11:18.166989+00:00
-- url     : https://prove2.me/theorems/e2e0e766-6851-4c32-b8a7-ed34a730adda
-- title:
--   Cyclic averaging removes off-diagonal operator blocks
-- statement:
--   Let $H$ be any complex Hilbert space and $n\geq1$. Set $\theta=\exp(2\pi i/n)$ and $E=\operatorname{diag}(\theta,\theta^2,\ldots,\theta^n)$. This scalar matrix is unitary, and its amplification to $H^n$ is unitary. Every operator block matrix $A=(a_{ij})\in B(H^n)$ satisfies
--   $$\frac1n\sum_{k=1}^n E^{-k}AE^k=\operatorname{diag}(a_{11},\ldots,a_{nn}).$$
--   Here the entries $a_{ij}$ are arbitrary bounded operators on $H$, without a self-adjointness restriction. The last diagonal value is $\theta^n=1$, and inverse powers are formally powers of the adjoint. This identity is the finite pinching operation used in the Jensen proof.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 6, Lemma 3.1: cyclic averaging removes off-diagonal blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Lemma 3.1, PDF p. 6, display (13).
Operator-valued blocks are arbitrary. Powers k.val+1 cover exactly k=1,...,n. -/
theorem cyclicAveraging (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Operators H)) :
    IsUnitaryMatrix (cyclicE n) ∧ IsUnitaryMatrix (operatorCyclicE H n) ∧
    (n : ℂ)⁻¹ • (∑ k : Fin n,
      (star (operatorCyclicE H n)) ^ (k.val + 1) * A *
        (operatorCyclicE H n) ^ (k.val + 1)) = Matrix.diagonal (fun i => A i i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
