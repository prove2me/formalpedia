-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_finiteDual_convolution_rationalPairing
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.finiteDual_convolution_rationalPairing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:56:07.180559+00:00
-- url     : https://prove2.me/theorems/17315248-cea5-4bd4-9ea5-fe114145182a
-- title:
--   Corollary 2.16
-- statement:
--   Let $R$ be a commutative noetherian unital ring and let $A$ be an associative unital $R$-algebra. Assume the canonical inclusion $A^\circ\hookrightarrow R^A$ is pure. The finite dual has its canonical coalgebra structure, characterized by $\Delta(f)(a\otimes b)=f(ab)$ and $\varepsilon(f)=f(1)$. Give $(A^\circ)^*=\operatorname{Hom}_R(A^\circ,R)$ its convolution algebra structure. Then
--
--   $$
--   (A^\circ,(A^\circ)^*,[-,-])\text{ is a rational pairing},
--   \qquad [f,\lambda]=\lambda(f).
--   $$
--
--   This supplies rationality against the convolution dual without a projectivity hypothesis on $A^\circ$.
--
--   **Formalization Note** The theorem concludes existence of the coalgebra with its canonical formulas, and rationality relative to that same structure. The coalgebra is not an independent hypothesis. `WithConv` selects Mathlib's convolution product on the dual.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 9, Corollary 2.16

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section ConvolutionPairing

variable {R C A : Type u} [CommRing R] [AddCommGroup C] [Module R C]

variable [Ring A] [Algebra R A]

/-- Corollary 2.16, PDF p.9: evaluation against the convolution dual is rational.
The canonical finite-dual coalgebra is supplied in the conclusion, with its defining formulas. -/
theorem finiteDual_convolution_rationalPairing [IsNoetherianRing R]
    (h : IsPureMap (R := R) (N := finiteDual R A) (L := A → R)
      (evaluationEmbedding (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A))) :
    ∃ c : Coalgebra R (finiteDual R A), IsCanonicalFiniteDualCoalgebra c ∧
      (letI : Coalgebra R (finiteDual R A) := c
       IsRationalPairing (R := R) (C := finiteDual R A)
         (A := WithConv (Module.Dual R (finiteDual R A)))
         (convolutionPairing (R := R) (C := finiteDual R A))) := by sorry

end ConvolutionPairing

end QAlgorithms.Papers.Independent.Gap48.P16

end
