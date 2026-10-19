-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_concaveFamilyCriterion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.concaveFamilyCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:03:30.541825+00:00
-- url     : https://prove2.me/theorems/b7e70f43-ddda-4dee-9f70-d7a2f8dd4505
-- title:
--   Proposition 2: concave coercive-family criterion
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   For convex $A$, $\mu$-compactness is equivalent to the existence of a family $F$ of concave functions $f:A\to[0,+\infty]$ such that
--   $$\overline{\{x\in A:f(x)\le c\}}\text{ is compact}\quad(f\in F,\ c>0),$$
--   and every compact $K\subseteq A$ admits $f\in F$ and a finite real $C$ with $f(x)\le C$ for all $x\in K$.
--
--   The criterion expresses tightness through concave coercive families; no lsc requirement is imposed on the family.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 4, Proposition 2: concave coercive-family criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LocallyConvexResults

variable {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

/-- Proposition 2, PDF pp.4–5: extended nonnegative concave coercive families.
No lower semicontinuity or finite-valuedness is added. -/
theorem concaveFamilyCriterion (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) :
    MuCompact A ↔ ∃ F : Set (E → ℝ≥0∞), CoerciveConcaveFamily A F := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
