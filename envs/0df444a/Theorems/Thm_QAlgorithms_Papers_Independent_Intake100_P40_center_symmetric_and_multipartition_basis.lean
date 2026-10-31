-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_center_symmetric_and_multipartition_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.center_symmetric_and_multipartition_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:14:00.545537+00:00
-- url     : https://prove2.me/theorems/8f90cc66-6fdc-4aa4-b483-f52c8cb69fc8
-- title:
--   Symmetric-polynomial center and explicit multipartition basis
-- statement:
--   Let $R$ be any commutative unital ring, let $l\ge1$ and $d\ge0$, and let $f(X)=X^l+\sum_{a=0}^{l-1}c_aX^a$ be monic. Let $H_d^f$ be the degenerate cyclotomic Hecke algebra with $s_ix_{i+1}=x_is_i+1$ and cyclotomic relation $f(x_1)=0$. For $d=0$ set $H_0^f=R$. Then
--
--   $$Z(H_d^f)=\{p(x_1,\ldots,x_d):p\in R[X_1,\ldots,X_d]^{S_d}\}.$$
--
--   More precisely, an explicit $R$-basis is
--
--   $$\{p_d(\phi(\lambda)):\lambda\in M_d(l)\}.$$
--
--   Here $M_d(l)$ consists of the $l$-tuples of partitions of total size $d$; $\phi$ replaces a part $a$ of color $r\in\{0,\ldots,l-1\}$ by $(a-1)l+r$ and removes resulting zero parts. For an ordinary partition $\eta$, $p_d(\eta)$ is the sum of the monomials obtained from its zero-padded $d$-tuple by distinct rearrangements. Thus the center is free with this specified multipartition-indexed basis, also over the zero ring.
--
--   This describes the center over arbitrary ground rings, without a characteristic or splitting assumption.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 2, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Theorem 1, PDF pp.2,12. Both symmetric-polynomial surjectivity and the
explicit multipartition-indexed basis p_d(phi(lambda)) are conclusions.
The coefficient tuple parametrizes every monic polynomial of degree l. -/
theorem center_symmetric_and_multipartition_basis (R : Type*) [CommRing R]
    (l d : ℕ) (hl : 0 < l) (c : Fin l → R) :
    (∀ z : CyclotomicAlgebra R l d c,
      z ∈ Subalgebra.center R (CyclotomicAlgebra R l d c) ↔
        ∃ p : MvPolynomial (Fin d) R, IsSymmetricPolynomial p ∧
          cyclotomicEvaluate R l d c p = z) ∧
    IsBasisFor
      (fun lam : Multipartition l d => cyclotomicP R l d c (partitionPhi l lam.val))
      (Subalgebra.center R (CyclotomicAlgebra R l d c)).toSubmodule := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
