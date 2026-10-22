-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_dicke_matrix_action
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.dicke_matrix_action
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:00:45.909594+00:00
-- url     : https://prove2.me/theorems/ab93b824-bac6-4838-af67-808b99f8d2d5
-- title:
--   Lemma D.2.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For every $\ell\ge0$ and arbitrary complex $M$,
--   $$M^{\otimes\ell}V^\ell=V^\ell T^\ell(M),\qquad V^{\ell\dagger}M^{\otimes\ell}V^\ell=T^\ell(M).$$
--   Columnwise these are precisely the Dicke-vector expansion and matrix-element identities (D.12).
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 66, Lemma D.2.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.66, Lemma D.2: vector expansion and matrix elements in Dicke coordinates. -/
theorem dicke_matrix_action (ell : ℕ) (M : Op (Fin 2)) :
    (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M *
        symmetricEmbedding ell = symmetricEmbedding ell * polynomialIrrep ell M) ∧
    (symmetricEmbedding ell)ᴴ * QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M *
      symmetricEmbedding ell = polynomialIrrep ell M := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
