-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_selected_marker_norm_limit
-- name    : WeilDefect.MarkerStability.finite_selected_marker_norm_limit
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T13:13:37.221364+00:00
-- url     : https://prove2.me/theorems/070d19c2-65ac-4236-b6c5-0f477396c6d7
-- title:
--   Original finite selected regularized markers have a norm limit
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces with $K$ finite dimensional. For a nonnegative bounded operator $L$ on $H$ and a bounded original selected synthesis $N:K\to H$, put $\Gamma_\varepsilon=(I+N^*(L+\varepsilon I)^{-1}N)^{-1}$. Then there is a positive contraction $G_0$ on $K$ such that
--   $$G_0=\inf_{\varepsilon>0}\Gamma_\varepsilon,\qquad\lim_{\varepsilon\downarrow0}\|\Gamma_\varepsilon-G_0\|=0.$$
--   The original inverse cost, coefficient carrier and norm are retained. The inverse cost need not stay bounded as $\varepsilon\downarrow0$; no range-inclusion, tail-rate or arithmetic positivity premise is needed.
-- source:
--   monocap-tech/weil at native base b019d40205680f9761a4b0a80cbcad56ee1b606b; new Screening/MarkerLimit.lean and Connes/CanonicalGreenMarkerLimit.lean. Exact certified sources in Connes_Weil_Original_Picard_Limit.zip. The inner norm limit is proved; critical support location, outer endpoint transfer and unconditional RH are not asserted.

import Definitions.Def_WeilMarker_regularized_cost
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
open scoped InnerProductSpace ComplexOrder Topology
open Filter Set WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.finite_selected_marker_norm_limit {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K]
    (L : H →L[ℂ] H) (hL : 0 ≤ L) (N : K →L[ℂ] H) :
    ∃ G₀ : K →L[ℂ] K, 0 ≤ G₀ ∧ G₀ ≤ 1 ∧
      IsGLB ((fun ε : ℝ => marker (L + ε • 1) N) '' Ioi 0) G₀ ∧
      Tendsto (fun ε : ℝ => marker (L + ε • 1) N)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by sorry
