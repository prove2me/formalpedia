-- Prove2me | Theorems.Thm_WeilDefect_RPB108_energy_lower_of_form_blocks
-- name    : WeilDefect.RPB108.energy_lower_of_form_blocks
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:54:40.726335+00:00
-- url     : https://prove2.me/theorems/b2551bbe-44b4-4749-82fb-7f64a4f1aa59
-- title:
--   Energy lower bound from realized form blocks
-- statement:
--   Let E be a complex inner-product space, T a continuous complex-linear map, and B a complex-valued form satisfying subtraction in both arguments and symmetry of its real part. The weak inverse equation is B(TR,u)=⟨R,u⟩ for every u. No boundedness of B is assumed. Let N,D,V,U,A,k,e be real numbers and z,p,q complex numbers. Assume e=N+2 Re⟨R,h−TR⟩+Re B(h−TR,h−TR), N−Re⟨R,TR⟩=D|z|²+2 Re(conj(z)(p−q))+U, A≤D, V≤U, and k‖h‖²≤Re B(h,h). Then A|z|²−2|z||p−q|+V+k‖h‖²≤e. No signs of A,k,V are added.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/FormCompletion.lean#L37-L56; exact native theorem WeilDefect.RPB108.energy_lower_of_form_blocks. SHA256 9d83ac9a57bec7771c1b9d156306326c08b8e3b9f013f38b02f37c875a13301c. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.energy_lower_of_form_blocks {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hsym : ∀ u v, (B u v).re = (B v u).re)
    (R h : E) (hsolve : ∀ u, B (T R) u = inner ℂ R u)
    (N D V actualRetained A k energy : ℝ) (z p q : ℂ)
    (hraw : energy = N+2*(inner ℂ R (h-T R)).re+(B (h-T R) (h-T R)).re)
    (hfinite : N-(inner ℂ R (T R)).re =
      D*‖z‖^2+2*(star z*(p-q)).re+actualRetained)
    (hD : A ≤ D) (hretained : V ≤ actualRetained)
    (hhigh : k*‖h‖^2 ≤ (B h h).re) :
    A*‖z‖^2-2*‖z‖*‖p-q‖+V+k*‖h‖^2 ≤ energy := by sorry
