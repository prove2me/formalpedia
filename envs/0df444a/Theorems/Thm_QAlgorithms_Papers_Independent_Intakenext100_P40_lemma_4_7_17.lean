-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P40_lemma_4_7_17
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P40.lemma_4_7_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:29:53.97747+00:00
-- url     : https://prove2.me/theorems/21063bb4-c922-41e1-ad98-f852ad5cca5a
-- title:
--   Finite-presentation closure over a left coherent ring
-- statement:
--   Let $R$ be an associative unital ring, not necessarily commutative. Suppose that $R$ is left coherent: every finitely generated left ideal of $R$ is finitely presented as a left $R$-module. Then the following hold.
--
--   1. For every integer $n\geq 0$, every finitely generated left submodule of $R^n$ is finitely presented.
--   2. Every finitely generated submodule of a finitely presented left $R$-module is finitely presented.
--   3. If $M$ and $N$ are finitely presented left $R$-modules and $f:M\to N$ is $R$-linear, then
--
--   $$
--   \ker(f)\quad\text{and}\quad\operatorname{coker}(f)=N/\operatorname{im}(f)
--   \quad\text{are finitely presented left }R\text{-modules}.
--   $$
--
--   These closure properties allow finite-presentation arguments over coherent rings, including the homotopy-group calculations for coherent ring spectra later in the paper.
--
--   **Formalization Note** A left ideal is represented as a submodule of the left regular module. Finite presentation uses Mathlib's predicate for modules over arbitrary rings. No nontriviality or commutativity hypothesis is imposed.
-- source:
--   Derived Algebraic Geometry II: Noncommutative Algebra, arXiv:math/0702299v5, PDF p. 164, Lemma 4.7.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P40

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P40

/-- Lemma 4.7.17, PDF p. 164 (proof continues on p. 165): over a left
coherent ring, finitely generated submodules of finite free or finitely presented
left modules are finitely presented, and kernels and cokernels of maps between
finitely presented left modules are finitely presented. All three clauses are
retained; the cokernel is the quotient of the codomain by the image. -/
theorem lemma_4_7_17 (R : Type u) [Ring R] (hR : leftCoherent R) :
    (∀ (n : ℕ) (S : Submodule R (Fin n → R)),
      S.FG → Module.FinitePresentation R S) ∧
    (∀ (M : Type v) [AddCommGroup M] [Module R M],
      Module.FinitePresentation R M →
        ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S) ∧
    (∀ (M : Type v) (N : Type w)
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
      Module.FinitePresentation R M → Module.FinitePresentation R N →
        ∀ f : M →ₗ[R] N,
          Module.FinitePresentation R (LinearMap.ker f) ∧
          Module.FinitePresentation R (N ⧸ LinearMap.range f)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P40
