-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_exists_compact_monotone_right_limit
-- name    : WeilDefect.MarkerStability.exists_compact_monotone_right_limit
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T13:13:17.786974+00:00
-- url     : https://prove2.me/theorems/5922bb9e-d1b4-4125-8c4c-d9352b9ebd08
-- title:
--   Compact monotone families in closed partial orders have right limits
-- statement:
--   Let $E$ be a topological partial order with closed order relation. Suppose $f:(0,\infty)\to E$ is increasing and takes values in a fixed compact set $C$. Then there is $G_0\in C$ such that
--   $$G_0=\inf\{f(\varepsilon):\varepsilon>0\},\qquad\lim_{\varepsilon\downarrow0}f(\varepsilon)=G_0.$$
--   The infimum denotes the greatest lower bound and is proved to exist here. No lattice structure or linear ordering on $E$ is assumed. This supplies the compactness argument for finite selected Green markers.
-- source:
--   monocap-tech/weil at native base b019d40205680f9761a4b0a80cbcad56ee1b606b; new Screening/MarkerLimit.lean and Connes/CanonicalGreenMarkerLimit.lean. Exact certified sources in Connes_Weil_Original_Picard_Limit.zip. The inner norm limit is proved; critical support location, outer endpoint transfer and unconditional RH are not asserted.

import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
open Filter Set
open scoped Topology

theorem WeilDefect.MarkerStability.exists_compact_monotone_right_limit{E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ ε : ℝ, 0 < ε → f ε ∈ C)
    (hmono : MonotoneOn f (Ioi (0 : ℝ))) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsGLB (f '' Ioi (0 : ℝ)) G₀ ∧
      Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by sorry
