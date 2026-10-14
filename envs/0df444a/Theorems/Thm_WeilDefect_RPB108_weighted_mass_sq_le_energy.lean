-- Prove2me | Theorems.Thm_WeilDefect_RPB108_weighted_mass_sq_le_energy
-- name    : WeilDefect.RPB108.weighted_mass_sq_le_energy
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:14.105797+00:00
-- url     : https://prove2.me/theorems/cf041046-8e71-435f-a1ba-e159e86433e1
-- title:
--   Weighted mass sq le energy
-- statement:
--   For every index type $\iota$, finite subset $s$ of $\iota$, and real-valued functions $w,L,z$ on $\iota$, if $L_i>0$ for every $i\in s$, then $\bigl(\sum_{i\in s}w_i|z_i|\bigr)^2\le\bigl(\sum_{i\in s}w_i^2/L_i\bigr)\bigl(\sum_{i\in s}L_i z_i^2\bigr)$. The weights $w_i$ and entries $z_i$ may have either sign, and there are no conditions on values outside $s$. The set $s$ may be empty, in which case both sides are zero; each denominator occurring in a nonempty sum is strictly positive.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; PhysicalGap.lean, line 9; SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.weighted_mass_sq_le_energy in WeilDefect/RPB108/PhysicalGap.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 95f803d0c4f97ab5bca884b54a1f222deb20306770f1fb4ba110a75828a1a958). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.weighted_mass_sq_le_energy {ι : Type*} (s : Finset ι)
    (w L z : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) :
    (∑ i ∈ s, w i * |z i|) ^ 2 ≤
      (∑ i ∈ s, (w i) ^ 2 / L i) * (∑ i ∈ s, L i * (z i) ^ 2) := by sorry
