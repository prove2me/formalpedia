-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_polynomial_irrep_properties
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.polynomial_irrep_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:56:22.590361+00:00
-- url     : https://prove2.me/theorems/c7a4b75b-1ece-46e8-950a-a96f58c318a2
-- title:
--   Appendix C.1–C.2: concrete representation properties
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For every $\ell\ge0$, the concrete matrices satisfy
--   $$T^\ell(AB)=T^\ell(A)T^\ell(B),\quad T^\ell(zM)=z^\ell T^\ell(M),\quad T^\ell(\operatorname{diag}(a,d))=\operatorname{diag}(a^{\ell-k}d^k).$$
--   They preserve identity, the zero-basis projector, transpose, entrywise conjugation and adjoint, and send unitary matrices to unitary matrices. An SVD $M=U\operatorname{diag}(a,d)V^\dagger$, $a,d\ge0$, is transported to $T^\ell(U)\operatorname{diag}(a^{\ell-k}d^k)T^\ell(V)^\dagger$. Thus its singular values are the stated monomials. The false rank-one aside at zero vectors is excluded.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 57, Appendix C.1–C.2: concrete representation properties

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

/-- PDF pp.59-60, Appendix C.2: all concrete polynomial representation
properties, including the SVD transport with its nonnegative singular values. -/
theorem polynomial_irrep_properties (ell : ℕ) :
    (∀ A B : Op (Fin 2), polynomialIrrep ell (A*B) = polynomialIrrep ell A * polynomialIrrep ell B) ∧
    (∀ (z : ℂ) (M : Op (Fin 2)), polynomialIrrep ell (z • M) = z^ell • polynomialIrrep ell M) ∧
    (∀ a d : ℂ, polynomialIrrep ell (Matrix.diagonal ![a,d]) =
      Matrix.diagonal (fun k : Fin (ell+1) => a^(ell-k.val)*d^k.val)) ∧
    polynomialIrrep ell 1 = 1 ∧
    polynomialIrrep ell (Matrix.single 0 0 1) = Matrix.single 0 0 1 ∧
    (∀ M : Op (Fin 2), polynomialIrrep ell M.transpose = (polynomialIrrep ell M).transpose ∧
      polynomialIrrep ell (fun i j => conj (M i j)) = (fun i j => conj (polynomialIrrep ell M i j)) ∧
      polynomialIrrep ell Mᴴ = (polynomialIrrep ell M)ᴴ) ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      (polynomialIrrep ell U.val)ᴴ * polynomialIrrep ell U.val = 1 ∧
      polynomialIrrep ell U.val * (polynomialIrrep ell U.val)ᴴ = 1) ∧
    (∀ (U V : Matrix.unitaryGroup (Fin 2) ℂ) (a d : ℝ), 0 ≤ a → 0 ≤ d →
      polynomialIrrep ell (U.val * Matrix.diagonal ![(a:ℂ),(d:ℂ)] * V.valᴴ) =
        polynomialIrrep ell U.val *
          Matrix.diagonal (fun k : Fin (ell+1) => ((a^(ell-k.val)*d^k.val : ℝ) : ℂ)) *
          (polynomialIrrep ell V.val)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
