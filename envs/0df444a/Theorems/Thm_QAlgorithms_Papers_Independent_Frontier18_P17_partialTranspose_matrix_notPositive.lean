-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_partialTranspose_matrix_notPositive
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.partialTranspose_matrix_notPositive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:37:05.374083+00:00
-- url     : https://prove2.me/theorems/01bc176f-f3d5-4fd2-b860-80fa51f28f8f
-- title:
--   First-subsystem partial transpose matrix and nonpositivity
-- statement:
--   On a two-qubit operator $X$, define first-subsystem partial transpose by $(T_1X)_{(a,b),(c,d)}=X_{(c,b),(a,d)}$, with $a,b,c,d\in\{0,1\}$. Let $T$ be one-qubit ordinary transpose, let $M_T$ and $M_{T_1}$ be the matrices in row-stacked coordinates, and let $P$ regroup $((a,b),(c,d))$ as $((a,c),(b,d))$. Then
--
--   $$M_{T_1}=P^{-1}(M_T\otimes I_4)P,\qquad
--   \neg\bigl[\forall X\succeq0,\ T_1(X)\succeq0\bigr].$$
--
--   Thus the stated permutation representation also applies to this linear map that is not completely positive, and partial transpose is not positive. The transposed subsystem is the first one.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 8, Example 6, Eqs.(66)–(67); Appendix A.3.b, PDF p.11

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.8, Example 6, Eqs. (66)–(67); p.11, Appendix A.3.b: first-factor
partial transpose on two qubits has this matrix and is not positive.
Transpose is not assumed CP. This is distinct from partial trace. -/
theorem partialTranspose_matrix_notPositive :
    superMatrix (partialTranspose (I := Fin 2) (J := Fin 2)) =
      unreshuffleMatrix (Fin 2) (Fin 2) *
        Matrix.kronecker (superMatrix (transposeMap 2))
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) * reshuffleMatrix (Fin 2) (Fin 2) ∧
    ¬ (∀ X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      X.PosSemidef → (partialTranspose X).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
