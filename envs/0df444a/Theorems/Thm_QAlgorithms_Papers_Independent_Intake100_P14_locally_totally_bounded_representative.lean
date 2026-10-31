-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_locally_totally_bounded_representative
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.locally_totally_bounded_representative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:14:48.66889+00:00
-- url     : https://prove2.me/theorems/66f4a1de-d686-44b9-b4f2-ba8cc9a02a5c
-- title:
--   Proposition 33: locally totally bounded representatives
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Every class has a Borel cocycle representative $\sigma:G^p\to A$ such that
--
--   $$\sigma(K)\text{ is totally bounded for every compact }K\subseteq G^p.$$
--
--   The representative belongs to the original cohomology class. This gives regularity on compact subsets without requiring global continuity.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 15, Proposition 33: locally totally bounded representatives

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

/-- Proposition 33, PDF p.15: a locally totally bounded Borel cocycle in the original
class, including the immediate one-point-domain degree zero. -/
theorem locally_totally_bounded_representative (p : ℕ) (f : GroupPower G p → A)
    (hf : IsCocycle mu T.act p f) :
    ∃ sigma : GroupPower G p → A, IsCocycle mu T.act p sigma ∧
      SameClass mu T.act p f sigma ∧ LocallyTotallyBounded sigma := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
