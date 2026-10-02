-- Prove2me | Theorems.Thm_TeschlQM_Spectral_spectrum_eq
-- name    : TeschlQM.Spectral.spectrum_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:31:40.252361+00:00
-- url     : https://prove2.me/theorems/14e56ddd-d8d9-4849-9262-e4d9c9a8b2e5
-- title:
--   Theorem 3.8 — the spectrum in terms of spectral projections
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$ and let $P_A$ be its projection-valued measure, the projection-valued measure with $A = \int_{\mathbb{R}} \lambda\, dP_A(\lambda)$ (unique by the spectral theorem). Then
--   $$\sigma(A) = \{\lambda \in \mathbb{R} \mid P_A((\lambda - \varepsilon, \lambda + \varepsilon)) \ne 0 \text{ for all } \varepsilon > 0\} \qquad (3.53).$$
--
--   Thus the spectrum is the support of the projection-valued measure; in particular it is real.
--
--   **Formalization Note.** $P_A$ enters as a projection-valued measure `P` with the hypothesis `A = spectralIntegral P (fun x => x)`; by the uniqueness part of Theorem 3.7 this is exactly $P_A$, so no generality is lost or gained. $\sigma(A)$ is the resolvent-based spectrum `TeschlQM.Spectral.spectrum` of p. 73 (a subset of $\mathbb{C}$), and the right-hand side is the image of the real set under $\mathbb{R} \hookrightarrow \mathbb{C}$. The hypothesis `IsSelfAdjoint A` is the book's; it also follows from the other two.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 97, Theorem 3.8

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_TeschlQM_Spectral_spectrum

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 97, Theorem 3.8. Let `A` be self-adjoint and `P_A` its projection-valued measure,
i.e. the projection-valued measure with `A = ∫_ℝ λ dP_A(λ)` (unique by Theorem 3.7). Then
`σ(A) = {λ ∈ ℝ | P_A((λ − ε, λ + ε)) ≠ 0 for all ε > 0}` (3.53). -/
theorem spectrum_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (P : Set ℝ → (H →L[ℂ] H))
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hAP : A = spectralIntegral P (fun x => (x : ℂ))) :
    spectrum A =
      (fun x : ℝ => (x : ℂ)) ''
        {x : ℝ | ∀ ε : ℝ, 0 < ε → P (Set.Ioo (x - ε) (x + ε)) ≠ 0} := by sorry

end TeschlQM.Spectral
