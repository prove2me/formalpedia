-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_regularized_covariance_le_iff_selected_correction
-- name    : WeilDefect.MarkerStability.regularized_covariance_le_iff_selected_correction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T22:22:17.523452+00:00
-- url     : https://prove2.me/theorems/f0e5c955-8b25-458e-88a1-7c4fe777a6fa
-- title:
--   Regularized physical covariance order reduces to a selected coefficient correction
-- statement:
--   For bounded operators P:K→H and N:L→H between complete complex inner-product spaces and δ>0, the comparison NN* ≤ PP*+δI is equivalent to nonnegativity on L of δI−N*N+(P*N)* (P*P+δI)⁻¹ (P*N). The inverse is the ring inverse of the positive regularized coefficient covariance. No finite dimension, independent columns, invertible unregularized Gram matrix, strict selected gap or RH premise is needed. The final correction lives on the selected coefficient space L.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/FiniteGram.lean and WeilDefect/Connes/FiniteSelectedCertificates.lean at compiling source head d28908eb3d61a4a81d7b4a5aff70ea26b6680897

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem WeilDefect.MarkerStability.regularized_covariance_le_iff_selected_correction (P : K →L[ℂ] H)
    (N : L →L[ℂ] H) (δ : ℝ) (hδ : 0 < δ) :
    N ∘L N.adjoint ≤ P ∘L P.adjoint + δ • 1 ↔
    0 ≤ δ • (1 : L →L[ℂ] L) - N.adjoint ∘L N +
      (P.adjoint ∘L N).adjoint ∘L Ring.inverse (P.adjoint ∘L P + δ • 1) ∘L
        (P.adjoint ∘L N) := by sorry
