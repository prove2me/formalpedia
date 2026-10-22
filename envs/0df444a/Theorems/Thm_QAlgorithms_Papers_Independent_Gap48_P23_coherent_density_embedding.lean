-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_coherent_density_embedding
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.coherent_density_embedding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:02:06.560554+00:00
-- url     : https://prove2.me/theorems/98da5398-b2f7-4789-8081-5bff99aded15
-- title:
--   Corollary D.4.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For any $\ell\ge0$ and arbitrary qubit vector $\psi$, the two arrows are
--   $$|\psi\rangle\langle\psi|\ \xmapsto{T^\ell}\ |\psi^\ell\rangle\langle\psi^\ell|\ \xmapsto{\Sigma^\ell}\ (|\psi\rangle\langle\psi|)^{\otimes\ell}.$$
--   Here $\Sigma^\ell(X)=V^\ell XV^{\ell\dagger}$ is linear, while $T^\ell$ generally is not.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 68, Corollary D.4.

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

/-- PDF p.68, Corollary D.4: T^ell is a polynomial map, not a linear channel
when ell>1; only the second arrow is an embedding channel. -/
theorem coherent_density_embedding (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep ell (pureDensity psi) = pureDensity (monomialKet ell psi) ∧
    symmetricEmbeddingChannel ell (polynomialIrrep ell (pureDensity psi)) =
      QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
