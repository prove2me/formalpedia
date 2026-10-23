-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_dual_cg_decomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.dual_cg_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:59:16.81034+00:00
-- url     : https://prove2.me/theorems/791a4d8a-945f-4be4-bccf-8cce91d99043
-- title:
--   Appendix C.7: explicit dual Clebsch–Gordan transform
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   The source matrix $D_\ell=C_\ell(S\otimes I)$ is unitary. For invertible $M$, with $M^*=(M^{-1})^T$,
--   $$D_\ell(M^*\otimes T^\ell(M))D_\ell^\dagger=T^{\ell-1}(M)\oplus\det(M)^{-1}T^{\ell+1}(M).$$
--   At $\ell=0$ the first sector is absent. Entrywise conjugation is not substituted for the dual on nonunitary matrices.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 64, Appendix C.7: explicit dual Clebsch–Gordan transform

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

/-- PDF pp.64-65, (C.49)-(C.54): dual means inverse transpose. Negative
determinant powers are used only at invertible M; ell=0 has an empty first sector. -/
theorem dual_cg_decomposition (ell : ℕ) :
    (dualCG ell)ᴴ * dualCG ell = 1 ∧ dualCG ell * (dualCG ell)ᴴ = 1 ∧
    ∀ M : Op (Fin 2), M.det ≠ 0 →
      dualCG ell * Matrix.kronecker M⁻¹.transpose (polynomialIrrep ell M) * (dualCG ell)ᴴ =
        blockDiagonal (lowerDualAction ell M) (M.det⁻¹ • polynomialIrrep (ell+1) M) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
