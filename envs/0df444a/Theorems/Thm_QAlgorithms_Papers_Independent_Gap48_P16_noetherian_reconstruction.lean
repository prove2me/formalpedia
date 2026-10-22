-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_noetherian_reconstruction
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.noetherian_reconstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:54:46.82816+00:00
-- url     : https://prove2.me/theorems/43326fda-fe9a-441f-bc1c-78f2e88884d5
-- title:
--   Lemma 2.13
-- statement:
--   Let $R$ be a commutative noetherian unital ring. For every set $S$, every $n\ge0$, and arbitrary functions $f_1,\ldots,f_n:S\to R$, there exist $m\ge0$, common points $s_1,\ldots,s_m\in S$, and common functions $g_1,\ldots,g_m:S\to R$ such that
--
--   $$\forall i,\ \forall s\in S,\qquad f_i(s)=\sum_{l=1}^m f_i(s_l)g_l(s).$$
--
--   In particular, for arbitrary $R$-modules $P,A$ and a bilinear pairing $b:P\times A\to R$, injectivity of $\alpha_R$ implies mock-projectivity relative to $b$. Empty input sets and zero-length reconstructions are allowed. The common reconstruction is uniform over the entire finite family.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 7, Lemma 2.13

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

/-- Lemma 2.13, PDF pp.7-8: simultaneous finite reconstruction and its corollary. -/
theorem noetherian_reconstruction [IsNoetherianRing R] :
    (∀ (S : Type u) (n : ℕ) (f : Fin n → S → R),
      ∃ (m : ℕ) (s : Fin m → S) (g : Fin m → S → R),
        ∀ i x, f i x = ∑ l, f i (s l) * g l x) ∧
    (∀ (b : P →ₗ[R] A →ₗ[R] R),
      Function.Injective (pairingAlpha b R) → IsMockProjective b) := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
