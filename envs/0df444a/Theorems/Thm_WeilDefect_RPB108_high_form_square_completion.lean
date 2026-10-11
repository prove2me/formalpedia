-- Prove2me | Theorems.Thm_WeilDefect_RPB108_high_form_square_completion
-- name    : WeilDefect.RPB108.high_form_square_completion
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:54:39.091099+00:00
-- url     : https://prove2.me/theorems/09ac52a9-b5ca-4058-bfa3-25d7dcab8ad4
-- title:
--   High-form square completion
-- statement:
--   Let E be a complex inner-product space, T a continuous complex-linear map, and B a complex-valued form satisfying subtraction in both arguments and symmetry of its real part. The weak inverse equation is B(TR,u)=⟨R,u⟩ for every u. No boundedness of B is assumed. For R,h in E satisfying that weak inverse equation, Re B(h−TR,h−TR)+2 Re⟨R,h−TR⟩ = Re B(h,h)−Re⟨R,TR⟩.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/FormCompletion.lean#L5-L19; exact native theorem WeilDefect.RPB108.high_form_square_completion. SHA256 9d83ac9a57bec7771c1b9d156306326c08b8e3b9f013f38b02f37c875a13301c. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.high_form_square_completion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hsym : ∀ u v, (B u v).re = (B v u).re)
    (R h : E) (hsolve : ∀ u, B (T R) u = inner ℂ R u) :
    (B (h-T R) (h-T R)).re+2*(inner ℂ R (h-T R)).re =
      (B h h).re-(inner ℂ R (T R)).re := by sorry
