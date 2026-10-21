-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_central_idempotents_from_characters
-- name    : QAlgorithms.Papers.Independent.Next46.P12.central_idempotents_from_characters
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:15:18.663132+00:00
-- url     : https://prove2.me/theorems/1bbf0e51-3c6f-4072-b2ac-ab1031c8cfbf
-- title:
--   Proposition A.1: central idempotents from trace characters
-- statement:
--   Let $A$ be a finite-dimensional split semisimple unital algebra over a field $k$. Choose a split presentation $A\cong\prod_{\lambda\in I}\operatorname{End}_k(V^\lambda)$, where the $V^\lambda$ are all its nonzero simple left modules, one per isomorphism class. Let $\epsilon(\lambda)$ be the inverse image of identity in block $\lambda$ and zero in the other blocks. For $z\in Z(A)$ write $a_\lambda$ for its scalar on $V^\lambda$, and let $\chi^\lambda(a)=\operatorname{tr}(a|_{V^\lambda})$. Assume $\operatorname{char}k=0$. Let $B=\{b_i:i\in H\}$ be any finite basis of $A$, and let $\rho(a)$ be the trace of left multiplication by $a$ on $A$. Define $M_{ij}=\rho(b_jb_i)$ and $r_i^\lambda=\chi^\lambda(1)\chi^\lambda(b_i)$. Then
--
--   $$\rho(a)=\sum_\lambda\chi^\lambda(1)\chi^\lambda(a),\qquad\det M\ne0,\qquad\epsilon(\lambda)=\sum_j(M^{-1}r^\lambda)_j b_j.$$
--
--   Equivalently, the system $Mc=r^\lambda$ has a unique coefficient vector $c$, and it reconstructs $\epsilon(\lambda)=\sum_jc_jb_j$.
--
--   The irreducible trace characters uniquely determine the central idempotents by an explicit invertible linear system.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 33, Proposition A.1: central idempotents from trace characters

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Proposition A.1, source PDF pp. 32–33. Invertibility is a conclusion. The
actual regular character is recovered from simple characters, and the inverse trace
matrix uniquely reconstructs the coefficients of each central idempotent. -/
theorem central_idempotents_from_characters [FiniteDimensional k A] [CharZero k]
    (D : SplitPresentation k A) {I : Type w} [Fintype I] [DecidableEq I] (b : Module.Basis I k A) :
    (∀ a : A, regularCharacter (k := k) a = ∑ lam : D.Label,
      simpleCharacter D lam 1 * simpleCharacter D lam a) ∧
    (traceMatrix b).det ≠ 0 ∧
    (∀ lam : D.Label,
      let r : I → k := fun i => simpleCharacter D lam 1 * simpleCharacter D lam (b i)
      let c : I → k := Matrix.mulVec ((traceMatrix b)⁻¹) r
      centralIdempotent D lam = ∑ i, c i • b i) ∧
    (∀ lam : D.Label, ∃! c : I → k,
      (∀ i, ∑ j, regularCharacter (k := k) (b j * b i) * c j =
        simpleCharacter D lam 1 * simpleCharacter D lam (b i)) ∧
      centralIdempotent D lam = ∑ i, c i • b i) := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
