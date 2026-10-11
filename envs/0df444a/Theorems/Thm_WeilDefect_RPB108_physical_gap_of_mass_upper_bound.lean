-- Prove2me | Theorems.Thm_WeilDefect_RPB108_physical_gap_of_mass_upper_bound
-- name    : WeilDefect.RPB108.physical_gap_of_mass_upper_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:23.630342+00:00
-- url     : https://prove2.me/theorems/73083dca-f0b2-4e50-845d-31eff903c0f3
-- title:
--   Physical gap of mass upper bound
-- statement:
--   For every index type $\iota$, finite subset $s$, real-valued functions $w,L,z$ on $\iota$, and real numbers $g$ and $m$, assume $L_i>0$ for each $i\in s$, $g\ge0$, $g\sum_{i\in s}w_i^2/L_i\le1$, $m\ge0$, and $m\le\sum_{i\in s}w_i|z_i|$. Then $gm^2\le\sum_{i\in s}L_i z_i^2$. Individual weights and entries may have either sign, but the mass hypothesis requires their displayed weighted absolute-value sum to be nonnegative; values outside $s$ are unrestricted. Zero gap and zero mass are allowed. If $s$ is empty, the hypotheses force $m=0$, and the conclusion is $0\le0$; denominators for indices in $s$ are strictly positive.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; PhysicalGap.lean, line 43; SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.physical_gap_of_mass_upper_bound in WeilDefect/RPB108/PhysicalGap.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.physical_gap_of_mass_upper_bound {ι : Type*} (s : Finset ι)
    (w L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) (gap : ℝ)
    (hgap : 0 ≤ gap)
    (hbound : gap * (∑ i ∈ s, (w i) ^ 2 / L i) ≤ 1)
    (z : ι → ℝ) (mass : ℝ) (hmass : 0 ≤ mass)
    (hupper : mass ≤ ∑ i ∈ s, w i * |z i|) :
    gap * mass ^ 2 ≤ ∑ i ∈ s, L i * (z i) ^ 2 := by sorry
