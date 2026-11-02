-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_cyclicity_criteria
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.cyclicity_criteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:27:04.113092+00:00
-- url     : https://prove2.me/theorems/a40c1fb5-e732-41d5-8695-ba821095d490
-- title:
--   Three equivalent cyclicity criteria for a forward-invariant subspace
-- statement:
--   Let $E$ be a complex Hilbert space, let $U$ be an algebraic unitary one-parameter group on $E$, and let $F\subseteq E$ be a linear subspace invariant under $U_t$ for every $t>0$. The following three conditions are equivalent:
--   1. The negative-time translates $U_tF$, $t<0$, span a dense subspace of $E$.
--   2. There is a dense linear subspace $D\subseteq E$ such that for every $v\in D$ there is a real threshold $T_v$ with $U_tv\in F$ for all $t\geq T_v$.
--   3. $F$ is $U$-cyclic, meaning that its full real-time orbit has dense linear span.
--   $$\overline{\operatorname{span}\!\bigcup_{t<0}U_tF}=E\quad\Longleftrightarrow\quad (2)\quad\Longleftrightarrow\quad\overline{\operatorname{span}\!\bigcup_{t\in\mathbb R}U_tF}=E.$$
--
--   This criterion requires neither closedness of $F$, reflection positivity, nor strong continuity.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 11, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 3.5, PDF p. 11. Eplus is an arbitrary algebraic subspace; neither
closedness, reflection positivity, nor continuity is assumed. The large-time
threshold in the middle condition depends on the vector. -/
theorem cyclicity_criteria [hHilbert : CompleteSpace E] (U : RealUnitaryAction (E := E)) (F : Submodule ℂ E)
    (hF : ∀ t : ℝ, 0 < t → ∀ x ∈ F, U.op t x ∈ F) :
    ((orbitSpan U F (Set.Iio 0)).topologicalClosure = ⊤ ↔
      ∃ D : Submodule ℂ E, Dense (D : Set E) ∧
        ∀ v : D, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → U.op t v ∈ F) ∧
    ((∃ D : Submodule ℂ E, Dense (D : Set E) ∧
        ∀ v : D, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → U.op t v ∈ F) ↔ IsCyclic U F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
