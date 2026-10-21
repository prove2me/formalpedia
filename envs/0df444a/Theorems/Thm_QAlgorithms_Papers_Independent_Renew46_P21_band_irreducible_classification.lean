-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P21_band_irreducible_classification
-- name    : QAlgorithms.Papers.Independent.Renew46.P21.band_irreducible_classification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:26:48.072617+00:00
-- url     : https://prove2.me/theorems/e4527fd9-49ac-44ed-a172-d024b3b490e3
-- title:
--   Degree-one classification of irreducible representations of a finite band
-- statement:
--   Let $S$ be a finite semigroup in which every element is idempotent, and let $K$ be any field. For each Green $\mathcal J$-class $J$ define $I_J=\{s\in S:J\not\subseteq S^1sS^1\}$. There is a simple right representation on the one-dimensional space $K$ with apex $J$ and scalar character
--
--   $$
--   \varphi_J(s)=\begin{cases}0,&s\in I_J,\\1,&s\notin I_J.\end{cases}
--   $$
--
--   Every simple right representation is finite dimensional of degree one and is isomorphic to exactly one of these representations. More explicitly, its space $M$ admits an intertwining $K$-linear isomorphism $f:M\to K$ with $f(ms)=\varphi_J(s)f(m)$; its apex is $J$. Simplicity includes nonzero algebra action, so the zero representation is excluded. This gives an exhaustive classification indexed by all $\mathcal J$-classes, without a restriction on the field's characteristic or algebraic closure.
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, PDF p. 7, Corollary 9, equation (2.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- Corollary 9 and (2.2), pp. 7--8: all simple representations of a finite band
have degree one. Each J-class has the displayed scalar representation as its
unique isomorphism class of simples; all simple representations are exhausted.
Existence is asserted on K itself, and uniqueness is by an intertwining linear equivalence. -/
theorem band_irreducible_classification {K : Type u} {S : Type v}
    [Field K] [Semigroup S] [Finite S] (hband : ∀ s : S, s * s = s) :
    (∀ J : JClass S, ∃ rho : RightSemigroupAction K S K,
      (∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k) ∧
      SemigroupSimple rho ∧ HasApex rho J) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module K M]
      (rho : RightSemigroupAction K S M), SemigroupSimple rho →
      FiniteDimensional K M ∧ Module.finrank K M = 1 ∧
        ∃! J : JClass S, HasApex rho J ∧ ScalarModel rho J) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P21
