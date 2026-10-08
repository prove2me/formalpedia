-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_negative_form_small_regularization
-- name    : WeilDefect.MarkerStability.negative_form_small_regularization
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T06:38:31.624293+00:00
-- url     : https://prove2.me/theorems/e26b4b88-adaf-4f81-80e1-4fb6104a61b9
-- title:
--   A negative physical selected form forbids marker half-bounds at all small regularization scales
-- statement:
--   Let $H,K,J$ be complete complex Hilbert spaces, $P:K\to H$ and $N:J\to H$ bounded syntheses, and $x\in H$ a direction with $q(x)=\|P^*x\|^2-\|N^*x\|^2<0$. Using the original selected marker $\Gamma(A,N)=(I+N^*A^{-1}N)^{-1}$, there is $\delta>0$ such that
--   $$0<\varepsilon<\delta\ \Longrightarrow\ \Gamma(PP^*+\varepsilon I,N)\not\succeq\tfrac12 I.$$
--   The negative physical margin therefore prevents a marker half-bound on an entire positive interval of Picard scales. No bounded selected-cost hypothesis, range-inclusion premise, arithmetic positivity claim, or endpoint-limit interchange is needed. This is a reduction from a negative form, not an assertion that an arbitrary given physical system has such a direction.
-- source:
--   monocap-tech/weil at native base b019d40205680f9761a4b0a80cbcad56ee1b606b, new WeilDefect/Screening/MarkerThreshold.lean and WeilDefect/Connes/CanonicalGreenMarkerObstruction.lean; exact checked new source in Connes_Weil_Quartet_Marker_Obstruction.zip. Original inverse and selected actor definitions are unchanged. This is a new formally verified reduction, not an unconditional arithmetic half-bound theorem.

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder
open WeilDefect.MarkerStability

theorem WeilDefect.MarkerStability.negative_form_small_regularization {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : K →L[ℂ] H) {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (N : J →L[ℂ] H) (x : H)
    (hneg : ‖P.adjoint x‖ ^ 2 - ‖N.adjoint x‖ ^ 2 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ (1 / 2 : ℝ) • (1 : J →L[ℂ] J) ≤ marker (P ∘L P.adjoint + ε • 1) N := by sorry
