-- Prove2me | Theorems.Thm_WeilDefect_RPB108_completed_column_norm_le
-- name    : WeilDefect.RPB108.completed_column_norm_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:04.231999+00:00
-- url     : https://prove2.me/theorems/cbbbb7bf-bde5-4bd2-886a-1e8185023786
-- title:
--   Completed column norm le
-- statement:
--   In every normed additive commutative group $E$ with a complex normed vector-space structure, without requiring completeness, let $T:E\to E$ be a continuous complex-linear map, let $x,u\in E$, and let $m,q,k,B$ be real numbers. If $k>0$, the operator norm satisfies $\|T\|\le1/k$, $\|x\|\le m$, $\|u\|^2\le q$, $m\le B$, and $q\le\bigl(k(B-m)\bigr)^2$, then $\|x-T(u)\|\le B$. These hypotheses imply $m,q,B\ge0$, although no separate sign assumptions on them are given. The denominator in the operator bound is exactly the positive $k$; zero vectors and equality in all non-strict bounds are permitted.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; SourceNormBounds.lean, line 38; SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.completed_column_norm_le in WeilDefect/RPB108/SourceNormBounds.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.completed_column_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : E) (m q k B : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hx : ‖x‖ ≤ m)
    (hsource : ‖source‖^2 ≤ q) (hm : m ≤ B)
    (hq : q ≤ (k*(B-m))^2) : ‖x-T source‖ ≤ B := by sorry
