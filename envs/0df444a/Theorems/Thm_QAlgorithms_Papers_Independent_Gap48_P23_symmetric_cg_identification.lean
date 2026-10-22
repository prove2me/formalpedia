-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetric_cg_identification
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetric_cg_identification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:04:56.006331+00:00
-- url     : https://prove2.me/theorems/79357cac-485f-4049-8553-ba32501c5b14
-- title:
--   Appendix D.5: symmetric-space CG realization
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For $\ell\ge1$, the source physical row-stacking map $C_{\rm Sym}$ and $D_{\rm Sym}=C_{\rm Sym}(S\otimes I_{2^\ell})$ obey
--   $$C_{\rm Sym}C_{\rm Sym}^\dagger=I,\quad C_{\rm Sym}^\dagger C_{\rm Sym}=I_2\otimes\Pi_\ell,\quad C_\ell=C_{\rm Sym}(I_2\otimes V^\ell),\quad D_\ell=D_{\rm Sym}(I_2\otimes V^\ell).$$
--   Thus the ambient maps are rectangular partial isometries, unitary only after restricting their input space.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 71, Appendix D.5: symmetric-space CG realization

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

/-- PDF pp.71-72, Appendix D.5: physical CG is a partial isometry on the
ambient tensor space, and becomes unitary on C^2 tensor Sym(ell). Includes both
ordinary and dual coordinate identifications with exact source phases. -/
theorem symmetric_cg_identification (ell : ℕ) (hell : 1 ≤ ell) :
    symmetricCG ell * (symmetricCG ell)ᴴ = 1 ∧
    (symmetricCG ell)ᴴ * symmetricCG ell = Matrix.kronecker (1 : Op (Fin 2)) (dickeColumnProjector ell) ∧
    ordinaryCG ell = symmetricCG ell * Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding ell) ∧
    dualCG ell = symmetricDualCG ell * Matrix.kronecker (1 : Op (Fin 2)) (symmetricEmbedding ell) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
