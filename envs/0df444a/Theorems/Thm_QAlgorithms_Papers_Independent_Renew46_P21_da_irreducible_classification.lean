-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P21_da_irreducible_classification
-- name    : QAlgorithms.Papers.Independent.Renew46.P21.da_irreducible_classification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:28:12.267838+00:00
-- url     : https://prove2.me/theorems/d0bd847c-f6ad-41b7-89eb-ef1b50c2fc49
-- title:
--   Degree-one classification for the finite DA case
-- statement:
--   Let $S$ be a finite semigroup all of whose subgroups are trivial and whose regular Green $\mathcal J$-classes are subsemigroups. Let $K$ be any field. For each regular $\mathcal J$-class $J$, put $I_J=\{s\in S:J\not\subseteq S^1sS^1\}$. There is a simple right representation on $K$, with apex $J$, given by
--
--   $$
--   \varphi_J(s)=\begin{cases}0,&s\in I_J,\\1,&s\notin I_J.\end{cases}
--   $$
--
--   Every simple right $KS$-module is finite dimensional of degree one and is isomorphic to exactly one of these scalar models: an isomorphism $f:M\to K$ satisfies $f(ms)=\varphi_J(s)f(m)$. The indexing classes are exactly the regular classes. This is the extension of Corollary 9 asserted in the paper's final paragraph; nonregular classes do not supply additional simple modules.
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, PDF p. 8, Final extension after Corollary 9

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- Final extension, p. 8: the same degree-one classification holds for finite
semigroups with trivial subgroups and multiplicatively closed regular J-classes.
Only regular classes index the scalar models; nonregular classes are not apexes. -/
theorem da_irreducible_classification {K : Type u} {S : Type v}
    [Field K] [Semigroup S] [Finite S]
    (hgroups : OnlyTrivialSubgroups S)
    (hregular : ∀ J : JClass S, RegularClass J →
      ∀ s ∈ J.val, ∀ t ∈ J.val, s * t ∈ J.val) :
    (∀ J : JClass S, RegularClass J → ∃ rho : RightSemigroupAction K S K,
      (∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k) ∧
      SemigroupSimple rho ∧ HasApex rho J) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module K M]
      (rho : RightSemigroupAction K S M), SemigroupSimple rho →
      FiniteDimensional K M ∧ Module.finrank K M = 1 ∧
        ∃! J : JClass S, HasApex rho J ∧ ScalarModel rho J) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P21
