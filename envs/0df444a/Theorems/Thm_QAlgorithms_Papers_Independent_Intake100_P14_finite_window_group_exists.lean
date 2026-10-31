-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_finite_window_group_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.finite_window_group_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:17:13.727884+00:00
-- url     : https://prove2.me/theorems/72908af0-9a75-4533-b1b5-4073e55dcf16
-- title:
--   Lemma 56: nonzero two-cocycles vanishing on finite squares
-- statement:
--   There exists a finitely generated group $\Gamma$ such that, for every finite subset $F\subseteq\Gamma$, there is an integer-valued two-cocycle $\psi$ for the trivial action satisfying
--
--   $$[\psi]\ne0\text{ in }H^2(\Gamma,\mathbb Z),\qquad \psi|_{F\times F}=0.$$
--
--   Finite generation means generation by a finite subset; nonzero refers to the cohomology class, so no one-cochain has coboundary equal to $\psi$. This supplies the group used in the subsequent failures of continuity.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 22, Lemma 56: nonzero 2-cocycles vanishing on finite squares

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

/-- Lemma 56, PDF pp.22--23: a finitely generated group with cohomologically nonzero
integer two-cocycles vanishing on every prescribed finite square. The group is existentially
constructed, rather than the desired conclusion being imposed on a fixed group as a hypothesis. -/
theorem finite_window_group_exists :
    ∃ (Gamma : Type u) (inst : Group Gamma),
      @IsFinitelyGenerated Gamma inst ∧ @FiniteWindowNontrivial Gamma inst := by sorry

end QAlgorithms.Papers.Independent.Intake100.P14

end
