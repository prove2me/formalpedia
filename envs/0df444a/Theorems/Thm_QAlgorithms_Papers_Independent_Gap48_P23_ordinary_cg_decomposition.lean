-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_ordinary_cg_decomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.ordinary_cg_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:58:37.788954+00:00
-- url     : https://prove2.me/theorems/309ae8d7-adaa-4c0d-98b9-eb1c716f3ac3
-- title:
--   Appendix C.6: explicit Clebsch–Gordan transform
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   The source-phase matrix $C_\ell$ is unitary and, for every complex $M$,
--   $$C_\ell(M\otimes T^\ell(M))C_\ell^\dagger=\det(M)T^{\ell-1}(M)\oplus T^{\ell+1}(M).$$
--   For $\ell=0$ the first summand is the zero-dimensional absent sector, not $T^0$. Boundary kets with zero coefficients are omitted.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 63, Appendix C.6: explicit Clebsch–Gordan transform

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

/-- PDF pp.63-64, (C.40)-(C.44): exact real CG phases, unitarity and the
full matrix decomposition. The first sector is empty at ell=0. -/
theorem ordinary_cg_decomposition (ell : ℕ) :
    (ordinaryCG ell)ᴴ * ordinaryCG ell = 1 ∧ ordinaryCG ell * (ordinaryCG ell)ᴴ = 1 ∧
    ∀ M : Op (Fin 2), ordinaryCG ell * Matrix.kronecker M (polynomialIrrep ell M) *
      (ordinaryCG ell)ᴴ = blockDiagonal (lowerCGAction ell M) (polynomialIrrep (ell+1) M) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
