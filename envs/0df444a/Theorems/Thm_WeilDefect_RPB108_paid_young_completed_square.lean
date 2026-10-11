-- Prove2me | Theorems.Thm_WeilDefect_RPB108_paid_young_completed_square
-- name    : WeilDefect.RPB108.paid_young_completed_square
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:35.219984+00:00
-- url     : https://prove2.me/theorems/c94e251e-988a-4d1a-a28e-5a65ae2315ae
-- title:
--   Paid young completed square
-- statement:
--   For all real numbers $A,M,\theta,x,y$ with the sole hypothesis $\theta<1$, the identity $Ax^2-2Mxy+y^2-\bigl((A-M^2/(1-\theta))x^2+\theta y^2\bigr)=\bigl(Mx-(1-\theta)y\bigr)^2/(1-\theta)$ holds. No sign restrictions are imposed on $A,M,x,y$, and $\theta$ may be negative or zero as well as positive below one. The denominator in both fractions is exactly $1-\theta$, which is strictly positive under the hypothesis; the mixed term on the left uses the signed product $xy$.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; PaidYoung.lean, line 6; SHA256 d415bac932305316f5d1919a5bcd6f97cb5d4a5dee52a7f825c4f2a929025a43. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.paid_young_completed_square in WeilDefect/RPB108/PaidYoung.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 d415bac932305316f5d1919a5bcd6f97cb5d4a5dee52a7f825c4f2a929025a43). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.paid_young_completed_square (A M theta x y : ℝ) (ht : theta < 1) :
    A*x^2-2*M*x*y+y^2-((A-M^2/(1-theta))*x^2+theta*y^2) =
      (M*x-(1-theta)*y)^2/(1-theta) := by sorry
