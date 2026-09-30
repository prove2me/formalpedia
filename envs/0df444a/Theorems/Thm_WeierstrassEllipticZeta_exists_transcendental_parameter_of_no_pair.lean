-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_transcendental_parameter_of_no_pair
-- name    : WeierstrassEllipticZeta.exists_transcendental_parameter_of_no_pair
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:25:22.161615+00:00
-- url     : https://prove2.me/theorems/447b7e10-10fc-4afb-8993-2f9747b006cd
-- title:
--   A family without an independent pair has one transcendental parameter
-- statement:
--   Let $(v_i)_{i=0}^{n-1}$ be a finite family of complex numbers, including the possibility $n=0$. Suppose no two entries at distinct indices are algebraically independent over $\mathbb Q$. Then
--
--   $$
--   \exists\theta\in\mathbb C\setminus\overline{\mathbb Q}\quad
--   \forall i,\quad v_i\text{ is algebraic over }\mathbb Q(\theta).
--   $$
--
--   The parameter is not required to belong to the family or the field it generates. Thus this formulation includes families consisting entirely of algebraic numbers. It converts pairwise algebraic dependence into a common coefficient field for transcendence arguments.
--
--   **Formalization Note.** The statement expresses algebraicity over the subalgebra $\mathbb Q[\theta]$. This is equivalent to algebraicity over its fraction field $\mathbb Q(\theta)$ by clearing denominators.
-- source:
--   Derived finite-family form of the maximal-independent-set argument in Stacks Project, Section 9.26, Lemma 9.26.3, https://stacks.math.columbia.edu/tag/030D; existence of a transcendental complex number follows from the cardinality bound for algebraic extensions, Lemma 9.8.9, https://stacks.math.columbia.edu/tag/09GK. Local proof uses Mathlib AlgebraicIndependent.option_iff_transcendental and Algebra.IsAlgebraic.cardinalMk_le_max.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Tactic.FinCases

namespace WeierstrassEllipticZeta

theorem exists_transcendental_parameter_of_no_pair {n : ℕ} (values : Fin n → ℂ)
    (hpair : ¬ HasAlgebraicallyIndependentPair values) :
    ∃ θ : ℂ, Transcendental ℚ θ ∧
      ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ}) (values i) := by sorry

end WeierstrassEllipticZeta
