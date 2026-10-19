-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_generalizedVesterstromOBrien
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.generalizedVesterstromOBrien
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:02:18.406257+00:00
-- url     : https://prove2.me/theorems/e70f15de-63e4-4cd9-8501-03e8ec81cb23
-- title:
--   Theorem 1, pp.14–16: generalized Vesterstrom–O’Brien theorem (original paper seed)
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Suppose $A$ is convex and $\mu$-compact, meaning that $b^{-1}(K)$ is compact for every compact $K\subseteq A$. Let (i) denote openness of midpoint mixing $A\times A\to A$; (ii) openness of $b:M(A)\to A$; (iii) openness of $b:M(\overline{\operatorname{extr}A})\to A$; (iv) continuity of $\operatorname{co}f$ for every bounded continuous real $f$; and (v) the same assertion for bounded continuous concave real $f$. Then
--   $$
--   \mathrm{(i)}\iff\mathrm{(ii)}\iff\mathrm{(iii)}\iff\mathrm{(iv)}\iff\mathrm{(v)}.
--   $$
--   If these conditions hold, $\operatorname{extr}A$ is closed.
--
--   This is the generalized Vesterstrom–O’Brien theorem on the source’s locally convex class.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 14, Theorem 1, pp.14–16: generalized Vesterstrom–O’Brien theorem (original paper seed)

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

/-- Theorem 1, PDF pp.14–16, including the continuation on p.15.
The measure domain in (iii) is closure(extr A), not extr A. -/
theorem generalizedVesterstromOBrien (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A) (hm : MuCompact A) :
    (StableConvexSet A ↔ BarycenterOpen A A) ∧
    (BarycenterOpen A A ↔ BarycenterOpen A (closure (A.extremePoints ℝ))) ∧
    (BarycenterOpen A (closure (A.extremePoints ℝ)) ↔ StrongCEProperty A) ∧
    (StrongCEProperty A ↔ CEProperty A) ∧
    (CEProperty A → IsClosed (A.extremePoints ℝ)) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
