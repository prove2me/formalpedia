-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_propertyLeft_tensor
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.propertyLeft_tensor
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:58:55.663151+00:00
-- url     : https://prove2.me/theorems/ab5c682c-01ef-46bc-939f-4eb2edbfa5e2
-- title:
--   Proposition 4.9
-- statement:
--   Let $R$ be a commutative noetherian unital ring, and let $A,B$ be associative unital $R$-algebras with property $P_\ell$. Use the usual algebra structure on $A\otimes_R B$. For every cofinite left ideal $K$ of this tensor algebra there are left ideals $I\subseteq A$ and $J\subseteq B$ such that $A/I$ and $B/J$ are finite projective over $R$ and
--
--   $$
--   \operatorname{im}(I\otimes_R B)+\operatorname{im}(A\otimes_R J)\subseteq K.
--   $$
--
--   Moreover, $A\otimes_R B$ has property $P_\ell$. The witnesses may depend on $K$, and all finiteness and projectivity refer to the base ring.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 14, Proposition 4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section AlgebraOperations

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Proposition 4.9, PDF p.14: the controlled ideal refinement and tensor-algebra closure. -/
theorem propertyLeft_tensor [IsNoetherianRing R] (hA : PropertyLeft R A) (hB : PropertyLeft R B) :
    (∀ K : Submodule (A ⊗[R] B) (A ⊗[R] B), IsCofiniteLeft R (A ⊗[R] B) K →
      ∃ (I : Submodule A A) (J : Submodule B B),
        Module.Finite R (LeftQuotient R A I) ∧ Module.Projective R (LeftQuotient R A I) ∧
        Module.Finite R (LeftQuotient R B J) ∧ Module.Projective R (LeftQuotient R B J) ∧
        tensorSubmoduleSum (I.restrictScalars R) (J.restrictScalars R) ≤ K.restrictScalars R) ∧
    PropertyLeft R (A ⊗[R] B) := by sorry

end AlgebraOperations

end QAlgorithms.Papers.Independent.Gap48.P16

end
