-- Prove2me | Theorems.Thm_WeilDefect_RPB108_paid_young_lower
-- name    : WeilDefect.RPB108.paid_young_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:30.2226+00:00
-- url     : https://prove2.me/theorems/22729540-809a-4e05-914e-74579731a441
-- title:
--   Paid young lower
-- statement:
--   For all real numbers $A,M,\theta,x,y$ satisfying only $\theta<1$, the inequality $(A-M^2/(1-\theta))x^2+\theta y^2\le Ax^2-2M|xy|+y^2$ holds. In particular, the quantification permits negative as well as zero or positive $M$, and imposes no sign conditions on $A,x,y$; $\theta$ may be any real number strictly below one, including negative values. The mixed term on the right uses $|xy|$, and the denominator on the left is exactly the strictly positive $1-\theta$; the asserted inequality is non-strict.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; PaidYoung.lean, line 14; SHA256 d415bac932305316f5d1919a5bcd6f97cb5d4a5dee52a7f825c4f2a929025a43. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.paid_young_lower in WeilDefect/RPB108/PaidYoung.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 d415bac932305316f5d1919a5bcd6f97cb5d4a5dee52a7f825c4f2a929025a43). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.paid_young_lower (A M theta x y : ℝ) (ht : theta < 1) :
    (A-M^2/(1-theta))*x^2+theta*y^2 ≤ A*x^2-2*M*|x*y|+y^2 := by sorry
