-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_noetherian_purity
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.noetherian_purity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:55:26.017001+00:00
-- url     : https://prove2.me/theorems/1c40f2c6-4350-4a3c-89a8-21fe897e69d9
-- title:
--   Remark 2.14: purity criterion without mock-projectivity assumption
-- statement:
--   Let $R$ be a commutative noetherian unital ring, $P,A$ arbitrary $R$-modules, and $b:P\times A\to R$ bilinear. Suppose $\alpha_R$ is injective, and embed $P$ into all functions $R^A$ by $p\mapsto b(p,-)$. For every $R$-module $M$,
--
--   $$P\hookrightarrow R^A\text{ is }M\text{-pure}\quad\Longleftrightarrow\quad\alpha_M\text{ is injective}.$$
--
--   Mock-projectivity is a consequence of the noetherian reconstruction lemma and is not an extra hypothesis.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 8, Remark 2.14: purity criterion without mock-projectivity assumption

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

/-- Remark 2.14, PDF p.8: no mock-projectivity hypothesis over a noetherian base. -/
theorem noetherian_purity [IsNoetherianRing R] (b : P →ₗ[R] A →ₗ[R] R)
    (h : Function.Injective (pairingAlpha b R)) :
    IsTensorInjective (evaluationEmbedding b) M ↔ Function.Injective (pairingAlpha b M) := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
