-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_integer_coefficient_union_not_surjective
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.integer_coefficient_union_not_surjective
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:17:51.904889+00:00
-- url     : https://prove2.me/theorems/7c32cd92-8cf5-45a7-96bd-ce912af2a246
-- title:
--   Proposition 57: failure of coefficient continuity in degree two
-- statement:
--   Let $\Gamma$ be a finitely generated group having the property of Lemma 56: every finite square admits an integer two-cocycle vanishing there with nonzero cohomology class. Let $A=\bigoplus_{j\in\mathbb N}\mathbb Z$ with trivial $\Gamma$-action, and let $A_n\cong\mathbb Z^n$ be its initial-coordinate subgroups. Then
--
--   $$\varinjlim_n H^2(\Gamma,A_n)\longrightarrow H^2(\Gamma,A)\quad\text{is not surjective}.$$
--
--   Equivalently, there is an $A$-valued two-cocycle cohomologous to no cocycle supported in a fixed initial block of coordinates. This shows why compactness of the base group in Theorem C matters.
--
--   **Formalization Note** The printed statement leaves its degree $p$ unspecified; degree two is the degree actually constructed by the proof.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 23, Proposition 57: coefficient colimit non-surjectivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

/-- Proposition 57, PDF p.23. SOURCE CORRECTION: the printed degree p is unspecified;
the proof constructs degree two, so this states degree two. Initial-coordinate inclusions
Z^n -> directSum_N Z have a nonsurjective map on the direct limit of cohomology. -/
theorem integer_coefficient_union_not_surjective (Gamma : Type u) [Group Gamma]
    (hfg : IsFinitelyGenerated Gamma) (hwindow : FiniteWindowNontrivial Gamma) :
    ∃ f : GroupPower Gamma 2 → IntegerDirectSum, IsAlgebraicCocycle 2 f ∧
      ∀ n : ℕ, ∀ sigma : GroupPower Gamma 2 → IntegerDirectSum,
        IsAlgebraicCocycle 2 sigma → HasInitialSupport n sigma →
        ¬ IsAlgebraicBoundary 2 (fun g => f g - sigma g) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P14

end
