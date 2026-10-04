-- Prove2me | Theorems.Thm_RelativeZimmer_isAmenableRel_orbit_of_isCoamenable
-- name    : RelativeZimmer.isAmenableRel_orbit_of_isCoamenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:57:44.927857+00:00
-- url     : https://prove2.me/theorems/06fa63ef-e1b4-4382-ae0a-b5c080959337
-- title:
--   Monod 2023, Proposition 4.7 — a co-amenable subgroup with amenable orbit relation makes the whole orbit relation amenable
-- statement:
--   Let a countable group $\Lambda$ act on a measurable space $X$ with a σ-finite measure $\mu$, each element acting measurably and preserving $\mu$-null sets (a non-singular action). Let $\Gamma \le \Lambda$ be a co-amenable subgroup. If the orbit relation of $\Gamma$, the pairs $(x, gx)$ with $g \in \Gamma$, is amenable with respect to $\mu$, then so is the orbit relation of $\Lambda$.
--
--   Co-amenability is `Monod.IsCoamenable`: a $\Lambda$-invariant finitely additive probability measure on $\Lambda/\Gamma$. Amenability of a relation is `Monod.IsAmenableRel` from the Monod bundle, the existence of a left invariant mean on the relation. Non-singularity is stated as the two hypotheses `hmeas` (each $x \mapsto gx$ is measurable) and `hnull` (preimages of null sets under it are null).
--
--   Monod states it on p. 12: "Let $\Lambda$ be a countable group with a non-singular action on a standard probability space $X$. Let $\Gamma < \Lambda$ be a co-amenable subgroup of $\Lambda$. If the orbit equivalence relation produced by $\Gamma$ on $X$ is amenable, then so is the relation produced by $\Lambda$." The statement here allows any measurable space with a σ-finite measure in place of a standard probability space, and uses the Monod bundle's notion of an amenable relation; Monod's proof goes through Hjorth's cocycle characterisation of amenability, while the proof here averages translates of an invariant mean for $\Gamma$ over $\Lambda/\Gamma$ against the invariant finitely additive probability.
-- source:
--   Monod, N., Some comments on piecewise-projective groups of the line, Groups Geom. Dyn. 19 (2025) 459–476, https://doi.org/10.4171/ggd/883 (arXiv:2305.00796, whose page numbers are used), p. 12, Proposition 4.7

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace RelativeZimmer

theorem isAmenableRel_orbit_of_isCoamenable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    {Λ : Type*} [Group Λ] [Countable Λ] [MulAction Λ X] (Γ : Subgroup Λ)
    (hmeas : ∀ g : Λ, Measurable (fun x : X => g • x))
    (hnull : ∀ (g : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0)
    (hco : Monod.IsCoamenable Γ)
    (hΓ : Monod.IsAmenableRel μ {p : X × X | ∃ g ∈ Γ, g • p.1 = p.2}) :
    Monod.IsAmenableRel μ {p : X × X | ∃ g : Λ, g • p.1 = p.2} := by
  sorry

end RelativeZimmer
