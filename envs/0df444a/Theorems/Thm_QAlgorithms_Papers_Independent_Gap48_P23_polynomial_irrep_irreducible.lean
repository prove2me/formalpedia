-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_polynomial_irrep_irreducible
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.polynomial_irrep_irreducible
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:57:47.087658+00:00
-- url     : https://prove2.me/theorems/1a16d467-5af6-4679-991f-702ad0ab85b8
-- title:
--   Lemma C.2.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For every $\ell\ge0$, the concrete $SU(2)$ representation $T^\ell$ is irreducible:
--   $$\mathcal S\text{ invariant under every }T^\ell(U),\ U\in SU(2)\quad\Longrightarrow\quad\mathcal S=\{0\}\text{ or }\mathcal S=\mathbb C^{\ell+1}.$$
--   The invariant subspace is complex-linear.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 60, Lemma C.2.

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

/-- PDF p.60, Lemma C.2: no nontrivial invariant complex subspace for the
concrete SU(2) action, including the one-dimensional ell=0 representation. -/
theorem polynomial_irrep_irreducible (ell : ℕ)
    (S : Submodule ℂ (Fin (ell+1) → ℂ))
    (hS : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, U.val.det = 1 →
      ∀ v ∈ S, (polynomialIrrep ell U.val).mulVec v ∈ S) : S = ⊥ ∨ S = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
