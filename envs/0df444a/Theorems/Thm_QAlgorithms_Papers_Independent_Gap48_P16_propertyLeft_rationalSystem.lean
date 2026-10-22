-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_propertyLeft_rationalSystem
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.propertyLeft_rationalSystem
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:56:35.795379+00:00
-- url     : https://prove2.me/theorems/46b77576-1ffe-4ef3-98bd-f4808a4e7106
-- title:
--   Proposition 4.2
-- statement:
--   Let $R$ be a commutative noetherian unital ring and $A$ an associative unital $R$-algebra with property $P_\ell$: every left ideal $I$ for which $A/I$ is finitely generated over $R$ contains a left ideal $J$ for which $A/J$ is finite projective over $R$. Then
--
--   $$(A^\circ,A,\operatorname{ev})\text{ is a rational system},\qquad
--   \operatorname{ev}(f,a)=f(a).$$
--
--   Equivalently, for every $R$-module $M$ the canonical map $M\otimes_R A^\circ\to\operatorname{Hom}_R(A,M)$ is injective. This obtains rationality without assuming a coalgebra structure or purity.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 12, Proposition 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

/-- Proposition 4.2, PDF p.12: property P-left makes the evaluation system rational. -/
theorem propertyLeft_rationalSystem [IsNoetherianRing R] (h : PropertyLeft R A) :
    IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A) := by sorry

end Cofinite

end QAlgorithms.Papers.Independent.Gap48.P16

end
