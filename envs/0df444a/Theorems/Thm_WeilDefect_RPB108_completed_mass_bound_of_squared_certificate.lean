-- Prove2me | Theorems.Thm_WeilDefect_RPB108_completed_mass_bound_of_squared_certificate
-- name    : WeilDefect.RPB108.completed_mass_bound_of_squared_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:36.835535+00:00
-- url     : https://prove2.me/theorems/9d6a5125-f809-4a90-ad67-b8a754cbfdac
-- title:
--   Completed mass bound of squared certificate
-- statement:
--   For all real numbers $m,q,k,B$ satisfying $k>0$, $m\le B$, and $q\le\bigl(k(B-m)\bigr)^2$, one has $m+(\sqrt q)/k\le B$. There is no assumed nonnegativity of $m$, $q$, or $B$; $m$ and $B$ may both be negative. The square root is total on the reals and equals zero if $q<0$, in which case the conclusion reduces to $m\le B$. The denominator is exactly $k>0$, and the square-root term is $(\sqrt q)/k$, rather than the square root of a quotient. Equality $m=B$ is allowed and then requires $q\le0$.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; SourceNormBounds.lean, line 26; SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.completed_mass_bound_of_squared_certificate in WeilDefect/RPB108/SourceNormBounds.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.completed_mass_bound_of_squared_certificate (m q k B : ℝ)
    (hk : 0 < k) (hm : m ≤ B) (hq : q ≤ (k*(B-m))^2) :
    m + Real.sqrt q/k ≤ B := by sorry
