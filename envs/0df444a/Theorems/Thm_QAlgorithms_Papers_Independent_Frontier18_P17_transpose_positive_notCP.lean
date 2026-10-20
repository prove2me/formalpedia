-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_transpose_positive_notCP
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.transpose_positive_notCP
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:34:45.991976+00:00
-- url     : https://prove2.me/theorems/d830a725-6274-4569-b177-69347211623a
-- title:
--   Transpose is positive but not completely positive
-- statement:
--   For every integer $N\ge1$, let $T_N:M_N(\mathbb C)\to M_N(\mathbb C)$ be ordinary transpose in the canonical basis. Then
--
--   $$X\succeq0\Longrightarrow T_N(X)\succeq0\quad\text{for every }X\in M_N(\mathbb C),\qquad T_2\text{ is not completely positive}.$$
--
--   Here complete positivity tests positivity after extension by every finite ancillary identity map. This supplies a positive map that is not a quantum channel.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 6, Example 3 and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.6, Example 3 and following paragraph: ordinary transpose is positive
in every positive dimension but is not completely positive on M_2. -/
theorem transpose_positive_notCP :
    (∀ N : ℕ, 0 < N → ∀ X : Matrix (Fin N) (Fin N) ℂ,
      X.PosSemidef → (transposeMap N X).PosSemidef) ∧
    ¬ QAlgorithms.Entanglement.IsCompletelyPositive (transposeMap 2) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
