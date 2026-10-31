-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_uniform_approximation_and_lifting
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.uniform_approximation_and_lifting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:19:51.827229+00:00
-- url     : https://prove2.me/theorems/f0cd7fae-0751-4ed6-b1ae-ef4cd3dea76c
-- title:
--   Uniform approximation and exact coefficient lifting
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Call a function regular if it is a uniform limit of functions locally constant outside individual closed Haar-null sets. Then both assertions hold:
--
--   1. Every continuous $f:G^p\to A$ is regular.
--   2. For every continuous surjective equivariant additive homomorphism $q:A\to B$ of Polish $G$-modules, every regular $f:G^p\to B$ has a regular lift $\widetilde f:G^p\to A$ satisfying
--
--   $$q\circ\widetilde f=f.$$
--
--   The lift is an exact lift of the specified function. These assertions provide the lifting-stable class of functions used by the regularization argument.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 49, Unnumbered two auxiliary regularity assertions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14

noncomputable section

open MeasureTheory Filter Set

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

section LocallyCompact

variable {G : Type u} [Group G] [TopologicalSpace G]
    [hTG : IsTopologicalGroup G] [hT2 : T2Space G]
    [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]
    [MeasurableSpace G] [hBG : BorelSpace G]
    {A : Type v} [AddCommGroup A] [MetricSpace A] [hTA : IsTopologicalAddGroup A]
    [hPA : PolishSpace A] [MeasurableSpace A] [hBA : BorelSpace A]
    (mu : Measure G) [hHaar : mu.IsHaarMeasure] (T : ModuleAction G A)

include hTG hT2 hLC hSC hBG hTA hPA hBA hHaar

/-- The two auxiliary assertions of Section 9.4, PDF p.49: uniform approximation of
continuous maps, and exact lifting through continuous coefficient quotients. The lift
postcomposes to the given function, without replacing it by a cohomologous function. -/
theorem uniform_approximation_and_lifting (p : ℕ) :
    (∀ f : GroupPower G p → A, Continuous f → UniformRegular (powerMeasure mu p) f) ∧
    (∀ (B : Type w) [AddCommGroup B] [MetricSpace B] [IsTopologicalAddGroup B]
      [PolishSpace B] (TB : ModuleAction G B) (q : A →+ B),
      Continuous q → Function.Surjective q →
      (∀ g a, q (T.act g a) = TB.act g (q a)) →
      ∀ f : GroupPower G p → B, UniformRegular (powerMeasure mu p) f →
      ∃ lift : GroupPower G p → A, (∀ g, q (lift g) = f g) ∧
        UniformRegular (powerMeasure mu p) lift) := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
