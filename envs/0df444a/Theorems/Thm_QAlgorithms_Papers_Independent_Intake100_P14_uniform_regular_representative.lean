-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_uniform_regular_representative
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.uniform_regular_representative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:19:25.953152+00:00
-- url     : https://prove2.me/theorems/ff5a8286-8c75-4247-a211-d5c15acc96e4
-- title:
--   Uniform approximation by maps with closed null exceptional sets
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Every class has a Borel cocycle representative $\sigma$ in the original class and functions $f_n:G^p\to A$ with closed sets $N_n\subseteq G^p$ such that
--
--   $$\mu_p(N_n)=0,\qquad f_n|_{G^p\setminus N_n}\text{ is locally constant},\qquad f_n\longrightarrow\sigma\text{ uniformly on }G^p.$$
--
--   The exceptional sets may depend on $n$. Uniform convergence refers to the compatible translation-invariant coefficient metric. This is the strengthening used to obtain the full-measure continuity set in Proposition 95.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 48, Unnumbered strengthening used to prove Proposition95

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

/-- The stronger regularity assertion used for Proposition 95, PDF pp.48--49.
UniformRegular retains the approximants and their individual closed Haar-null exceptional sets. -/
theorem uniform_regular_representative (p : ℕ) (f : GroupPower G p → A)
    (hf : IsCocycle mu T.act p f) :
    ∃ sigma : GroupPower G p → A, IsCocycle mu T.act p sigma ∧
      SameClass mu T.act p f sigma ∧ UniformRegular (powerMeasure mu p) sigma := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
