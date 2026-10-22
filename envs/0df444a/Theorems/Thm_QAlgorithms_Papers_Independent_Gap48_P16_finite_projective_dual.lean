-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_finite_projective_dual
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.finite_projective_dual
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:54:24.477414+00:00
-- url     : https://prove2.me/theorems/ee615350-368b-4cf8-8e29-f07fe03c3897
-- title:
--   Remark 2.12: finite projective algebra dual
-- statement:
--   Let $R$ be a commutative noetherian unital ring and let $A$ be an associative unital $R$-algebra, finite and projective as an $R$-module. Write $A^*=\operatorname{Hom}_R(A,R)$ and $A^\circ$ for its finite dual. Then
--
--   $$
--   A^\circ=A^*,\qquad A^\circ\hookrightarrow R^A\text{ is pure},\qquad
--   \pi:A^*\otimes_R A^*\longrightarrow(A\otimes_R A)^*\text{ is bijective},
--   $$
--
--   where $\pi(f\otimes g)(a\otimes b)=f(a)g(b)$. The final assertion is the canonical linear dual-tensor isomorphism, equivalently written in the source with the inverse orientation. No algebra isomorphism of ordinary duals is asserted.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 7, Remark 2.12: finite projective algebra dual

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

/-- Remark 2.12, PDF p.7: equality of duals, purity in all functions, and canonical tensor duality. -/
theorem finite_projective_dual [IsNoetherianRing R] [Module.Finite R A]
    [Module.Projective R A] :
    finiteDual R A = ⊤ ∧
    IsPureMap (R := R) (N := finiteDual R A) (L := A → R)
      (evaluationEmbedding (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) ∧
    Function.Bijective (TensorProduct.dualDistrib R A A) := by sorry

end Cofinite

end QAlgorithms.Papers.Independent.Gap48.P16

end
