-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P12_central_spectrum_trace
-- name    : QAlgorithms.Papers.Independent.Next46.P12.central_spectrum_trace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:10:42.216228+00:00
-- url     : https://prove2.me/theorems/989683ab-2c20-4594-907e-811ed53a82e1
-- title:
--   Proposition 2.4: spectrum by normalized trace character
-- statement:
--   Let $A$ be a finite-dimensional split semisimple unital algebra over a field $k$. Choose a split presentation $A\cong\prod_{\lambda\in I}\operatorname{End}_k(V^\lambda)$, where the $V^\lambda$ are all its nonzero simple left modules, one per isomorphism class. Let $\epsilon(\lambda)$ be the inverse image of identity in block $\lambda$ and zero in the other blocks. For $z\in Z(A)$ write $a_\lambda$ for its scalar on $V^\lambda$, and let $\chi^\lambda(a)=\operatorname{tr}(a|_{V^\lambda})$. Assume $\operatorname{char}k=0$. For every central element $z$ and every $\lambda\in I$,
--
--   $$\chi^\lambda(1)\ne0,\qquad a_\lambda=\frac{\chi^\lambda(z)}{\chi^\lambda(1)}.$$
--
--   The scalar spectrum can be obtained from actual trace characters, including repeated eigenvalues.
-- source:
--   Canonical idempotents of multiplicity-free families of algebras, arXiv:1606.08900v5, PDF p. 9, Proposition 2.4: spectrum by normalized trace character

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

noncomputable section

open scoped BigOperators Classical

open Filter

namespace QAlgorithms.Papers.Independent.Next46.P12

universe u v w

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Proposition 2.4, source PDF p. 9. No center-generator condition is imposed;
repeated eigenvalues are permitted. Characteristic zero makes the denominator nonzero. -/
theorem central_spectrum_trace [FiniteDimensional k A] [CharZero k]
    (D : SplitPresentation k A) (z : Subalgebra.center k A) (i : D.Label) :
    simpleCharacter D i 1 ≠ 0 ∧
    centralSpectrum D (z : A) i = simpleCharacter D i (z : A) / simpleCharacter D i 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P12

end
