-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P14_small_crossed_homomorphism
-- name    : QAlgorithms.Papers.Independent.Intake100.P14.small_crossed_homomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:16:09.694484+00:00
-- url     : https://prove2.me/theorems/797abc2c-929a-4b84-a96c-f1913b5e0fdf
-- title:
--   Lemma 35: small crossed homomorphisms
-- statement:
--   Let $G$ be a compact Hausdorff second countable group with probability Haar measure $\mu$. Let $(A,\rho,T)$ be a Polish Abelian $G$-module with a compatible translation-invariant and action-invariant metric. Let $\alpha:G\to A$ be Borel and satisfy the crossed equation $\alpha(hg)=T(h)\alpha(g)+\alpha(h)$ Haar almost everywhere. If $0<\varepsilon<1/2$ and $\mu\{g:\rho(0,\alpha(g))>\varepsilon\}<\varepsilon$, then
--
--   $$\operatorname*{ess\,sup}_{g\in G}\rho(0,\alpha(g))\le2\varepsilon.$$
--
--   This upgrades probabilistic smallness of a one-cocycle to an essential uniform bound.
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, PDF p. 16, Lemma 35: small crossed homomorphisms

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

/-- Lemma 35, PDF p.16: essential uniform distance at most 2 epsilon for an epsilon-small
Borel crossed homomorphism with epsilon<1/2. Its crossed equation is understood a.e.,
following the standing convention for cochain identities in Section 2. -/
theorem small_crossed_homomorphism [CompactSpace G] [IsProbabilityMeasure mu]
    (hiso : ActionIsometric T) (alpha : G → A) (hBorel : Measurable alpha)
    (hcrossed : ∀ᵐ z ∂mu.prod mu, alpha (z.1 * z.2) =
      T.act z.1 (alpha z.2) + alpha z.1)
    (epsilon : ℝ) (hsmall : Small mu alpha epsilon) (hepsilon : epsilon < 1 / 2) :
    uniformDistance mu (fun _ => 0) alpha ≤ ENNReal.ofReal (2 * epsilon) := by sorry

end LocallyCompact

end QAlgorithms.Papers.Independent.Intake100.P14

end
