-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_exists_compact_antitone_right_limit
-- name    : WeilDefect.MarkerStability.exists_compact_antitone_right_limit
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T14:05:23.386036+00:00
-- url     : https://prove2.me/theorems/eae318aa-17ed-4f77-afb4-84c16df0bd14
-- title:
--   Compact antitone families have right limits characterized by least upper bounds
-- statement:
--   Let $E$ be a topological partial order with closed order relation, $c\in\mathbb R$, and $f:(c,\infty)\to E$ a decreasing family contained in a compact set $C$. There is $G_+\in C$ with
--   $$G_+=\sup\{f(t):t>c\},\qquad\lim_{t\downarrow c}f(t)=G_+.$$
--   The supremum is the least upper bound and is proved to exist without assuming a lattice or total order on $E$. Applied to the original finite selected Picard markers, this supplies their outer support norm limit after their inner regularization norm limits.
-- source:
--   monocap-tech/weil native base b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source modules Connes/CanonicalGreenWindowInclusion.lean, Screening/MarkerCompression.lean and Connes/CanonicalGreenSupportLimit.lean in Connes_Weil_Original_Support_Limit.zip. Both ordered norm limits are proved natively; prescribed critical endpoint identification, support containment, arithmetic lower bounds and RH are not assumed or asserted.

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
open Filter Set
open scoped Topology

theorem WeilDefect.MarkerStability.exists_compact_antitone_right_limit{E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (c : ℝ) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ t : ℝ, c < t → f t ∈ C)
    (hanti : AntitoneOn f (Set.Ioi c)) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsLUB (f '' Set.Ioi c) G₀ ∧
      Filter.Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds G₀) := by sorry
