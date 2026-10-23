-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P46_section_value_one_sided
-- name    : QAlgorithms.Papers.Independent.Gap48.P46.section_value_one_sided
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:05:43.660996+00:00
-- url     : https://prove2.me/theorems/ef6896d8-5fab-4ef3-8523-e3da214919e3
-- title:
--   Appendix II: equality optimum is a one-sided optimum
-- statement:
--   Let $S$ be a nonempty compact convex subset of a finite-dimensional real normed vector space, $F:S\to\mathbb R$ continuous and concave, and $l$ real linear. Write $f,f_+,f_-$ for the attained maxima of $F$ over $l(x)=\alpha$, $l(x)\le\alpha$, and $l(x)\ge\alpha$, respectively. For every $\alpha\in l(S)$,
--
--   $$f(\alpha)=f_+(\alpha)\quad\text{or}\quad f(\alpha)=f_-(\alpha).$$
--
--   The choice of side may depend on $\alpha$, and both equalities may hold. The result identifies a one-sided constraint preserving each equality-section optimum.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, PDF p. 17, Appendix II: equality optimum is a one-sided optimum

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

/-- PDF p.17, Appendix II: the one-sided choice is inside the quantifier over alpha. -/
theorem section_value_one_sided {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (S : Set V) (hS : S.Nonempty) (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (F : V → ℝ) (hcontinuous : ContinuousOn F S)
    (hconcave : ConcaveOn ℝ S F) (l : V →ₗ[ℝ] ℝ) :
    ∀ alpha ∈ sectionDomain S l (· = ·),
      sectionValue S F l (· = ·) alpha = sectionValue S F l (· ≤ ·) alpha ∨
      sectionValue S F l (· = ·) alpha = sectionValue S F l (· ≥ ·) alpha := by sorry

end QAlgorithms.Papers.Independent.Gap48.P46

end
