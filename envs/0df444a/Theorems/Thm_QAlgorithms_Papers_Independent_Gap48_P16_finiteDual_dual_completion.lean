-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_finiteDual_dual_completion
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.finiteDual_dual_completion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:57:30.208868+00:00
-- url     : https://prove2.me/theorems/f0a155f0-9028-4713-aa92-b6b457da8584
-- title:
--   Remark 4.5: finite-dual dual and cofinite completion
-- statement:
--   Let $R$ be a commutative noetherian unital ring and $A$ an associative unital $R$-algebra with property $P_\ell$. Let $\widehat A$ be the $R$-module of all families $(a_I)$, indexed by cofinite left ideals $I$, with $a_I\in A/I$ and compatible under the quotient transitions $A/I\to A/J$ for $I\subseteq J$. There is a canonical $R$-linear isomorphism
--
--   $$
--   \Phi:\operatorname{Hom}_R(A^\circ,R)\ \xrightarrow{\ \sim\ }\ \widehat A,
--   \qquad f\bigl(\Phi(\lambda)_I\bigr)=\lambda(f\circ q_I),
--   $$
--
--   for every cofinite $I$ and $f\in(A/I)^*$, where $q_I:A\to A/I$ is the quotient map and $f\circ q_I$ is regarded as an element of $A^\circ$. This identifies the finite-dual dual with the cofinite completion as modules; left-ideal quotients are not treated as algebras.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 13, Remark 4.5: finite-dual dual and cofinite completion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

/-- Remark 4.5, PDF p.13: the canonical R-linear cofinite-completion isomorphism. -/
theorem finiteDual_dual_completion [IsNoetherianRing R] (h : PropertyLeft R A) :
    ∃ e : Module.Dual R (finiteDual R A) ≃ₗ[R] cofiniteCompletion R A,
      ∀ (l : Module.Dual R (finiteDual R A)) (I : CofiniteLeftIdeal R A)
        (f : Module.Dual R (LeftQuotient R A I.val)),
        l (cofiniteDualElement R A I f) = f ((e l).val I) := by sorry

end Cofinite

end QAlgorithms.Papers.Independent.Gap48.P16

end
