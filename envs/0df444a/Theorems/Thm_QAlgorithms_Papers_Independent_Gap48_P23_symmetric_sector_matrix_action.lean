-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetric_sector_matrix_action
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetric_sector_matrix_action
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:04:15.257719+00:00
-- url     : https://prove2.me/theorems/fef31941-3baf-4722-99a5-2971758d250b
-- title:
--   Lemma D.7.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For $\ell\ge1$ and arbitrary complex $M$, the two physical-sector matrix elements are
--   $$\langle s_{\ell+1}(j)|M^{\otimes(\ell+1)}|s_{\ell+1}(k)\rangle=T^{\ell+1}(M)_{jk},$$
--   $$\langle s'_{\ell-1}(j)|M^{\otimes(\ell+1)}|s'_{\ell-1}(k)\rangle=\det(M)T^{\ell-1}(M)_{jk}.$$
--   Indices range over the actual respective dimensions.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 70, Lemma D.7.

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

/-- PDF p.70, Lemma D.7: both physical-sector matrix-element formulas. -/
theorem symmetric_sector_matrix_action (ell : ℕ) (hell : 1 ≤ ell) (M : Op (Fin 2)) :
    (∀ j k : Fin (ell+2), inner ℂ (pairDicke ell j.val)
      (WithLp.toLp 2 ((Matrix.kronecker M
        (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M)).mulVec
        (pairDicke ell k.val))) = polynomialIrrep (ell+1) M j k) ∧
    (∀ j k : Fin ell, inner ℂ (primedDicke ell j)
      (WithLp.toLp 2 ((Matrix.kronecker M
        (QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell M)).mulVec
        (primedDicke ell k))) = lowerCGAction ell M j k) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
