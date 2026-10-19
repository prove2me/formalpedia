-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_completelyEntangledSubspace
-- name    : QAlgorithms.Papers.Independent.Information100.P21.completelyEntangledSubspace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:11:20.32878+00:00
-- url     : https://prove2.me/theorems/e280678e-6710-45b6-a277-77572ca8fdb7
-- title:
--   IX.A–B — two-dimensional completely entangled subspace
-- statement:
--   In $\mathbb C^2\otimes\mathbb C^3$, let $E$ be the span of $|00\rangle+|11\rangle$ and $|01\rangle+|12\rangle$. Then
--   $$\dim E=2,\qquad E\text{ contains no nonzero product vector}.$$
--   The coefficient matrix of a combination is $\begin{pmatrix}x&y&0\\0&x&y\end{pmatrix}$, with corner minors $x^2,y^2$. This isolates the geometric failure of the two-qubit product-vector step.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 2, IX.A–B — two-dimensional completely entangled subspace

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 2, two-dimensional completely entangled subspace. -/
theorem completelyEntangledSubspace  :
  Module.finrank ℂ (Submodule.span ℂ (Set.range entangledPair))=2 ∧
  ∀ p : Vec QT, p∈Submodule.span ℂ (Set.range entangledPair) → p≠0 →
    ¬∃ (e : Vec (Fin 2)) (f : Vec (Fin 3)), p=tensor e f := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
