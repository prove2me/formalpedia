-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_mockProjective_purity
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.mockProjective_purity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:53:17.136783+00:00
-- url     : https://prove2.me/theorems/248812b3-d646-4c0a-b4c5-9f7c90fc1e80
-- title:
--   Proposition 2.7
-- statement:
--   Let $R$ be a commutative unital ring and let $b:P\times A\to R$ be bilinear. Suppose $P$ is mock-projective relative to this pairing: $\alpha_R$ is injective, and each finite family $p_i$ admits common points $a_l\in A$ and arbitrary functions $g_l:A\to R$ with $b(p_i,x)=\sum_l b(p_i,a_l)g_l(x)$. Embed $P$ into $R^A$ by $p\mapsto b(p,-)$. For every $R$-module $M$,
--
--   $$
--   P\hookrightarrow R^A\text{ is }M\text{-pure}\ \Longleftrightarrow\ \alpha_M\text{ is injective},
--   \qquad
--   (P,A,b)\text{ is rational}\ \Longleftrightarrow\ P\hookrightarrow R^A\text{ is pure}.
--   $$
--
--   Purity is injectivity after tensoring with the indicated module, or with every module in the second equivalence. This criterion concerns all functions on $A$, not only its linear dual.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 5, Proposition 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

/-- Proposition 2.7, PDF p.5: fixed-module and universal purity criteria. -/
theorem mockProjective_purity (b : P →ₗ[R] A →ₗ[R] R) (h : IsMockProjective b) :
    (IsTensorInjective (evaluationEmbedding b) M ↔ Function.Injective (pairingAlpha b M)) ∧
      (IsRationalSystem b ↔ IsPureMap (evaluationEmbedding b)) := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
