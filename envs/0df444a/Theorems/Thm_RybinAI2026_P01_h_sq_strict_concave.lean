-- Prove2me | Theorems.Thm_RybinAI2026_P01_h_sq_strict_concave
-- name    : RybinAI2026.P01.h_sq_strict_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T02:42:34.571873+00:00
-- url     : https://prove2.me/theorems/3567543a-b4e3-47ad-a904-deb2a49123c3
-- title:
--   Strict concavity of the squared reciprocal-J function
-- statement:
--   For fixed positive a, the function b -> (1/J(a,b))^2 is strictly concave on (0,infinity), where J(a,b) is the integral over [0,1] of 1/(a+(b-a)t^2). The second derivative is (2/j^4)(3(j')^2-j*j'') < 0 by a strict Cauchy-Schwarz moment comparison whose margin at infinity is exactly (pi/8)c^{-7/2}.
-- source:
--   P01 synthesis 2026-10-04, Agent A commuting-planar programme Lemma L2c (H^2 concavity). Coordinator analytic proof complete (closed-form route: atan/atanh one-line derivative checks with 4var^4 numerators; E(0)=-1/15; sharp (pi/8)c^{-7/2} margin). StrictConcaveOn presence-confirmed in pinned rev 0df444a3 (signature remote-checked at proof time). Math-audit UNSUPPORTED_SEMANTICS-advisory (same class as published L1e child); remote Lean verifier authoritative. v2 fixes argument order + explicit scalar field: pinned-revision source (Mathlib/Analysis/Convex/Function.lean @0df444a3) declares `variable (ᵕc) ... (s : Set E) (f : E → β)` with all explicit, so the application is `StrictConcaveOn ℝ s f`; v1 passed (fun, set) and failed elaboration.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

namespace RybinAI2026.P01

/-- For fixed `a > 0`, the squared reciprocal-J function `fun b => (1 / J(a,b))^2` with `J(a,b) = integral t in (0:Real)..1, (a + (b - a) * t^2)^{-1}` is strictly concave on `(0,infty)`. Proof route (closed-form, verified): homogeneity to c=(b-a)/a, j(c); (h^2)''<0 iff E:=3(j')^2-j*j''<0. For c>0 (u=sqrt(c)): E<0 iff atan(u)>3u/(3+u^2), proved by f(0)=0 and f'=4u^4/((1+u^2)(3+u^2)^2)>0. For c<0 (w=sqrt(-c)): E<0 iff atanh(w)>3w/(3-w^2), proved by f(0)=0 and f'=4w^4/((1-w^2)(3-w^2)^2)>0. At c=0: E=-1/15. Inputs: L1b/c closed forms + differentiation under the integral sign (L1d). The moment/CS route is superseded (still valid); margin at infinity (pi/8)c^{-7/2}, m2-tail R^{-1} warning retained. This is Lemma L2c of the commuting-planar programme; L3/L5 depend on it. -/
theorem h_sq_strict_concave (a : ℝ) (ha : 0 < a) :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun b => ((∫ t in (0 : ℝ)..1, (a + (b - a) * t ^ 2)⁻¹)⁻¹) ^ 2) := by sorry

end RybinAI2026.P01
