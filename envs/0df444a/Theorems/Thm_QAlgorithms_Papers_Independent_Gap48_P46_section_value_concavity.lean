-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_section_value_concavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.section_value_concavity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:04:59.656597+00:00
-- url     : https://prove2.me/theorems/0f847bdd-ef43-44ca-ac4f-ca4241962475
-- title:
--   Appendix II: three value functions are concave
-- statement:
--   Let $S$ be a nonempty compact convex subset of a finite-dimensional real normed vector space, $F:S\to\mathbb R$ continuous and concave, and $l$ a real linear functional. For each relation $R$ among $=$, $\le$, $\ge$, let $D_R=\{\alpha:\exists x\in S,\ l(x)\,R\,\alpha\}$. Then the three value functions
--
--   $$f_R(\alpha)=\max_{x\in S:\ l(x)\,R\,\alpha}F(x),\qquad R\in\{=,\le,\ge\},$$
--
--   are concave on their respective domains $D_R$, and all maxima there are attained. This is full concavity, with no optimized value asserted on empty sections.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 17, Appendix II: three value functions are concave

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.17, Appendix II: all three value functions are concave on their
nonempty-section domains, and every value in each domain is attained. -/
theorem section_value_concavity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (S : Set V) (hS : S.Nonempty) (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (F : V → ℝ) (hcontinuous : ContinuousOn F S)
    (hconcave : ConcaveOn ℝ S F) (l : V →ₗ[ℝ] ℝ) :
    ConcaveOn ℝ (sectionDomain S l (· = ·)) (sectionValue S F l (· = ·)) ∧
    ConcaveOn ℝ (sectionDomain S l (· ≤ ·)) (sectionValue S F l (· ≤ ·)) ∧
    ConcaveOn ℝ (sectionDomain S l (· ≥ ·)) (sectionValue S F l (· ≥ ·)) ∧
    (∀ rel : ℝ → ℝ → Prop, rel = (· = ·) ∨ rel = (· ≤ ·) ∨ rel = (· ≥ ·) →
      ∀ alpha ∈ sectionDomain S l rel,
        MaximizesValue (sectionSet S l rel alpha) F (sectionValue S F l rel alpha)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
