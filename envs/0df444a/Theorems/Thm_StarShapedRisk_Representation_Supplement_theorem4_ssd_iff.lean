-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem4_ssd_iff
-- name    : StarShapedRisk.Representation.Supplement.theorem4_ssd_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:47:32.332518+00:00
-- url     : https://prove2.me/theorems/7a7c8645-ec85-43bb-a872-37b6ff116b30
-- title:
--   Theorem 4 — star-shaped SSD-consistent risk measures as robustified ES
-- statement:
--   Fix an atomless probability space and let $\mathcal X=L^\infty(P)$, represented by bounded measurable functions. For any function $\rho:\mathcal X\to\mathbb R$, the following are equivalent: $\rho$ is a star-shaped, SSD-consistent risk measure; and there exists a star-shaped set $\mathcal G$ of increasing functions $g:(0,1)\to\mathbb R$, each satisfying $g(0+)\le0$, such that
--   $$\rho(X)=\inf_{g\in\mathcal G}\sup_{\alpha\in(0,1)}\{\operatorname{ES}_\alpha(X)-g(\alpha)\}\qquad(X\in\mathcal X).$$
--   SSD compares every increasing concave utility of the gains $-X$; law invariance is not assumed separately. This characterizes exactly the SSD-consistent subclass of star-shaped risk measures.
--
--   **Formalization Note** The infimum and supremum in the representation are taken in the extended reals. For increasing $g$, $g(0+)$ is its extended-real infimum on $(0,1)$.
--
--   Differences from the source:
--   - encoding: L∞ equivalence classes and g(0+) → published bounded measurable representatives and the extended-real infimum of g; reason: reuse the published carrier; SSD-consistency identifies almost-sure equal representatives and monotonicity identifies the one-sided limit
--   - encoding: the inf–sup in (24) → infimum and supremum in EReal, with ES−g formed in ℝ before embedding; reason: retain possibly infinite inner suprema without default values or indeterminate extended-real subtraction
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2646, Theorem 4

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_SSD
import Definitions.Def_StarShapedRisk_Representation_Supplement_ExpectedShortfall

namespace StarShapedRisk.Representation.Supplement

theorem theorem4_ssd_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (hP : StarShapedRisk.LawInvariant.IsAtomless P)
    (ρ : StarShapedRisk.LawInvariant.Positions Ω → ℝ) :
    (StarShapedRisk.LawInvariant.IsRiskMeasure ρ ∧
      StarShapedRisk.LawInvariant.IsStarShaped ρ ∧ IsSSDConsistent P ρ) ↔
      ∃ G : Set (Set.Ioo (0 : ℝ) 1 → ℝ),
        StarConvex ℝ 0 G ∧
        (∀ g ∈ G, Monotone g ∧ (⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal)) ≤ 0) ∧
        ∀ X : StarShapedRisk.LawInvariant.Positions Ω,
          (ρ X : EReal) =
            ⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, ((ES P α X - g α : ℝ) : EReal) := by sorry

end StarShapedRisk.Representation.Supplement
