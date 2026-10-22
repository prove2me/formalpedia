-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_complex_schur_algebra
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.complex_schur_algebra
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:04:12.175161+00:00
-- url     : https://prove2.me/theorems/ae5e2a0e-4597-43c3-89f8-e8944090a005
-- title:
--   Corollary 1.12
-- statement:
--   For $d>0$, let $S$ be a full irreducible complex Clifford module for $\mathbb C^d$ with its complex bilinear metric. Its complex Schur algebra is the centralizer of the even Clifford action in complex-linear endomorphisms. Then
--   $$C_d^{\mathbb C}\cong\begin{cases}\mathbb C\oplus\mathbb C,&d\text{ even},\\\mathbb C,&d\text{ odd}.\end{cases}$$
--   The statement concerns complex algebra isomorphisms and does not pass to underlying real modules.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 16, Corollary 1.12

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Corollary 1.12, PDF p. 16: the complex Schur algebra, with complex-linear commutant. -/
theorem complex_schur_algebra (d : ℕ) (hd : 0 < d)
    (S : Type*) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    if Even d then Nonempty (schurAlgebra rho ≃ₐ[ℂ] (ℂ × ℂ))
    else Nonempty (schurAlgebra rho ≃ₐ[ℂ] ℂ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
