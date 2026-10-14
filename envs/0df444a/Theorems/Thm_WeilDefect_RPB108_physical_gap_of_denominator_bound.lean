-- Prove2me | Theorems.Thm_WeilDefect_RPB108_physical_gap_of_denominator_bound
-- name    : WeilDefect.RPB108.physical_gap_of_denominator_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:13:59.964573+00:00
-- url     : https://prove2.me/theorems/f22a342e-187a-4d0d-a3ed-bf1e316e9ffc
-- title:
--   Physical gap of denominator bound
-- statement:
--   For every index type $\iota$, finite subset $s$, real-valued functions $w,L$ on $\iota$, and real number $g\ge0$, assume $L_i>0$ for all $i\in s$ and $g\sum_{i\in s}w_i^2/L_i\le1$. Then for every real-valued function $z$ on $\iota$, $g\bigl(\sum_{i\in s}w_i|z_i|\bigr)^2\le\sum_{i\in s}L_i z_i^2$. The weights and entries may have either sign, values outside $s$ are unrestricted, and $g=0$ is allowed. The set $s$ may be empty, yielding $0\le0$ and a denominator-bound hypothesis $0\le1$; otherwise the displayed denominators are strictly positive.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; PhysicalGap.lean, line 22; SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.physical_gap_of_denominator_bound in WeilDefect/RPB108/PhysicalGap.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.physical_gap_of_denominator_bound {ι : Type*} (s : Finset ι)
    (w L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) (gap : ℝ)
    (hgap : 0 ≤ gap)
    (hbound : gap * (∑ i ∈ s, (w i) ^ 2 / L i) ≤ 1)
    (z : ι → ℝ) :
    gap * (∑ i ∈ s, w i * |z i|) ^ 2 ≤ ∑ i ∈ s, L i * (z i) ^ 2 := by sorry
