-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_frechet_comparison
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.frechet_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:13:53.213023+00:00
-- url     : https://prove2.me/theorems/f8777553-4381-4106-9527-048fc146121f
-- title:
--   Theorem A: Frechet continuous and measurable comparison
-- statement:
--   Let $G$ be a Hausdorff locally compact second countable group, let $A$ be a Polish Abelian topological group with a jointly continuous action $T$ by automorphisms, and let $p\ge0$. Cochains are Borel maps on $G^p$, cocycle and coboundary equations hold Haar almost everywhere, and $d$ is the unnormalized inhomogeneous bar differential. In degree zero, $C^0=A$ and $B^0=0$. Suppose moreover that $A$ is a real Fréchet space in its given topology. The natural map induced by the inclusion of continuous cochains is an isomorphism:
--
--   $$H^p_{\mathrm{cts}}(G,A)\longrightarrow H^p_{\mathrm m}(G,A).$$
--
--   Explicitly, every Borel cocycle is cohomologous to a continuous cocycle, and every continuous cocycle which is a measurable coboundary has a continuous primitive. If $G$ is compact and $p>0$, then $H^p_{\mathrm m}(G,A)=0$.
--
--   This identifies the continuous bar theory with the measurable theory for Fréchet coefficients.
--
--   **Formalization Note** Both surjectivity and injectivity are expressed through their exact representative-level conditions; no unspecified cohomology group or comparison map is assumed.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 7, Theorem A: continuous/measurable Frechet comparison (paper seed)

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

/-- Theorem A, PDF p.7, proof pp.18--19: surjectivity and injectivity of the natural
continuous-to-measurable comparison, in its exact bar-representative formulation, and
vanishing in positive degrees for compact G and Frechet A. -/
theorem frechet_comparison [Module ℝ A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
    (p : ℕ) :
    (∀ f : GroupPower G p → A, IsCocycle mu T.act p f →
      ∃ sigma : GroupPower G p → A, Continuous sigma ∧ IsCocycle mu T.act p sigma ∧
        SameClass mu T.act p f sigma) ∧
    (∀ f : GroupPower G p → A, Continuous f → IsCocycle mu T.act p f →
      IsMeasurableBoundary mu T.act p f → IsContinuousBoundary T.act p f) ∧
    (CompactSpace G → 0 < p → ∀ f : GroupPower G p → A,
      IsCocycle mu T.act p f → IsMeasurableBoundary mu T.act p f) := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
