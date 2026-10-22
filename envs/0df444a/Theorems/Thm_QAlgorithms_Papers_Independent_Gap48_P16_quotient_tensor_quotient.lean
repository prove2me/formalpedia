-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_quotient_tensor_quotient
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.quotient_tensor_quotient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:58:35.106514+00:00
-- url     : https://prove2.me/theorems/1fadc7ec-4eba-4a05-a754-1a2f25a14247
-- title:
--   Lemma 4.8
-- statement:
--   Let $R$ be a commutative noetherian unital ring, $M,N$ arbitrary $R$-modules, and $I\subseteq M$, $J\subseteq N$ submodules. Suppose $I$ is $N$-pure and $J$ is $M$-pure. Let $L$ be the sum of the images of $I\otimes_R N$ and $M\otimes_R J$ in $M\otimes_R N$. There is a canonical $R$-linear isomorphism
--
--   $$
--   (M/I)\otimes_R(N/J)\ \xrightarrow{\ \sim\ }\ (M\otimes_R N)/L,
--   \qquad (m+I)\otimes(n+J)\longmapsto m\otimes n+L.
--   $$
--
--   This retains the source's purity assumptions; flatness of both $M$ and $N$ is an alternative sufficient condition for them. The denominator is a sum of images, not their intersection.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 14, Lemma 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section TensorQuotients

variable {R M N : Type u} [CommRing R]

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Lemma 4.8, PDF p.14, retaining the printed purity hypotheses and the canonical map. -/
theorem quotient_tensor_quotient [IsNoetherianRing R] (I : Submodule R M) (J : Submodule R N)
    (hI : IsTensorInjective I.subtype N) (hJ : IsTensorInjective J.subtype M) :
    ∃ e : (M ⧸ I) ⊗[R] (N ⧸ J) ≃ₗ[R] (M ⊗[R] N) ⧸ tensorSubmoduleSum I J,
      ∀ (m : M) (n : N), e (I.mkQ m ⊗ₜ[R] J.mkQ n) =
        (tensorSubmoduleSum I J).mkQ (m ⊗ₜ[R] n) := by sorry

end TensorQuotients

end QAlgorithms.Papers.Independent.Gap48.P16

end
