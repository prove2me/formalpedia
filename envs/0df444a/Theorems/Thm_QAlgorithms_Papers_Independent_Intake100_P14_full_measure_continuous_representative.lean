-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_full_measure_continuous_representative
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.full_measure_continuous_representative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:18:28.769363+00:00
-- url     : https://prove2.me/theorems/27653c13-bba2-43db-a047-ce00e4c4368d
-- title:
--   Proposition 95: full-measure G-delta continuity
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Every class has a Borel cocycle representative $\sigma:G^p\to A$ and a dense $G_\delta$ subset $S\subseteq G^p$ such that
--
--   $$\mu_p(G^p\setminus S)=0,\qquad \sigma|_S\text{ is continuous}.$$
--
--   Here $\mu_p$ is product Haar measure, with mass one on the degree-zero domain. The class of $\sigma$ equals the original class. This describes regularity of representatives without claiming continuity at every point of $G^p$.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 48, Proposition 95: full-measure G-delta continuity

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

/-- Proposition 95, PDF p.48, discussion pp.48--49: a Borel representative whose
restriction to a dense, full-Haar-measure G-delta set is continuous. -/
theorem full_measure_continuous_representative (p : ℕ) (f : GroupPower G p → A)
    (hf : IsCocycle mu T.act p f) :
    ∃ sigma : GroupPower G p → A, IsCocycle mu T.act p sigma ∧
      SameClass mu T.act p f sigma ∧ ∃ S : Set (GroupPower G p),
        IsGδ S ∧ powerMeasure mu p Sᶜ = 0 ∧ Dense S ∧ ContinuousOn sigma S := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
