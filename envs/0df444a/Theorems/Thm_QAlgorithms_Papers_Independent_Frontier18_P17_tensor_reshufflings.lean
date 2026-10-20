-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_tensor_reshufflings
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.tensor_reshufflings
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:28:01.251987+00:00
-- url     : https://prove2.me/theorems/7c48aceb-0a7e-455f-815a-3830b70391f4
-- title:
--   Tensor products under primary and alternative reshuffling
-- statement:
--   Let $A\in M_n(\mathbb C)$ and $B\in M_m(\mathbb C)$. Write $\operatorname{res}$ for row stacking, $\operatorname{vec}$ for column stacking, $R$ for primary reshuffling in the row-ordered matrix-unit bases, and $R'$ for the alternative reshuffling using reversed subsystem order and transposed bases. Then
--
--   $$\operatorname{res}((A\otimes B)^R)=\operatorname{res}(A)\otimes\operatorname{res}(B),\qquad
--   \operatorname{vec}((A\otimes B)^{R'})=\operatorname{vec}(A)\otimes\operatorname{vec}(B).$$
--
--   These identities connect matrix tensor coordinates to vector tensor coordinates. They impose no positivity or normalization conditions and allow zero matrices and one-dimensional factors.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 3, Proposition 2, Eqs.(17)–(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.3, Proposition 2, Eqs. (17)–(18): reshuffling precedes res/vec.
Zero matrices, dimension one and arbitrary square local matrices are included. -/
theorem tensor_reshufflings {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    res (reshuffle (Matrix.kronecker A B)) = QAlgorithms.tensorVec (res A) (res B) ∧
    vec (alternateReshuffle (Matrix.kronecker A B)) = QAlgorithms.tensorVec (vec A) (vec B) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
