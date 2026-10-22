-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_coherent_embedding
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.coherent_embedding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:01:26.94567+00:00
-- url     : https://prove2.me/theorems/499717db-0e78-494e-8428-31483d611767
-- title:
--   Proposition D.3.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For any $\ell\ge0$ and arbitrary qubit vector $\psi$,
--   $$V^\ell|\psi^\ell\rangle=|\psi\rangle^{\otimes\ell}.$$
--   No normalization restriction is imposed; empty tensor powers are included.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 68, Proposition D.3.

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

/-- PDF p.68, Proposition D.3: exact vector identity, with no normalization
assumption on psi and with the empty tensor power included. -/
theorem coherent_embedding (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    WithLp.toLp 2 ((symmetricEmbedding ell).mulVec (monomialKet ell psi)) =
      QAlgorithms.Papers.Independent.Support21.P18.physicalPower ell psi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
