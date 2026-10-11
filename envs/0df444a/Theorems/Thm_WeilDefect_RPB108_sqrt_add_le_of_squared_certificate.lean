-- Prove2me | Theorems.Thm_WeilDefect_RPB108_sqrt_add_le_of_squared_certificate
-- name    : WeilDefect.RPB108.sqrt_add_le_of_squared_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:13:58.687398+00:00
-- url     : https://prove2.me/theorems/4ae78ae8-aada-402a-a48d-8c6ace383f98
-- title:
--   Sqrt add le of squared certificate
-- statement:
--   For all real numbers $a,b,M$ satisfying $a\ge0$, $b\ge0$, $M\ge0$, $M^2-a-b\ge0$, and $4ab\le(M^2-a-b)^2$, one has $\sqrt a+\sqrt b\le M$. Square roots are the total real square-root function, which returns zero on negative arguments, although here both arguments are required to be nonnegative. Every hypothesis and the conclusion use non-strict inequalities, so zero arguments, zero residual, and $M=0$ are included; when $M=0$, the hypotheses force $a=b=0$.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; SourceNormBounds.lean, line 9; SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.sqrt_add_le_of_squared_certificate in WeilDefect/RPB108/SourceNormBounds.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.sqrt_add_le_of_squared_certificate (a b M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (he : 0 ≤ M^2-a-b) (hc : 4*a*b ≤ (M^2-a-b)^2) :
    Real.sqrt a + Real.sqrt b ≤ M := by sorry
