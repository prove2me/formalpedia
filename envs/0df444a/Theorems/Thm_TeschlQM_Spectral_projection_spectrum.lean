-- Prove2me | Theorems.Thm_TeschlQM_Spectral_projection_spectrum
-- name    : TeschlQM.Spectral.projection_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:32:10.937963+00:00
-- url     : https://prove2.me/theorems/21fabd95-48ae-4288-898a-75f00603f462
-- title:
--   Corollary 3.9 — $P_A(\sigma(A)) = \mathbb{I}$ and $P_A(\mathbb{R}\cap\rho(A)) = 0$
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$ and let $P_A$ be its projection-valued measure ($A = \int_{\mathbb{R}} \lambda\, dP_A(\lambda)$). Then
--   $$P_A(\sigma(A)) = \mathbb{I} \qquad\text{and}\qquad P_A(\mathbb{R} \cap \rho(A)) = 0 \qquad (3.54).$$
--
--   Consequently $P_A(f) = P_A(\chi_{\sigma(A)} f)$: functions of $A$ only depend on the values of $f$ on the spectrum.
--
--   **Formalization Note.** As in Theorem 3.8, $P_A$ is a projection-valued measure `P` with `A = spectralIntegral P (fun x => x)`. The sets $\sigma(A)$ and $\mathbb{R} \cap \rho(A)$ are subsets of $\mathbb{C}$; they enter as the real sets $\{x \in \mathbb{R} \mid x \in \sigma(A)\}$ and $\{x \in \mathbb{R} \mid x \in \rho(A)\}$ (both Borel, since $\sigma(A)$ is closed).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 97, Corollary 3.9

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_TeschlQM_Spectral_spectrum

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 97, Corollary 3.9. Let `A` be self-adjoint and `P_A` its projection-valued
measure (`A = ∫_ℝ λ dP_A(λ)`). Then `P_A(σ(A)) = 𝕀` and `P_A(ℝ ∩ ρ(A)) = 0` (3.54), where the
subsets `σ(A)` and `ℝ ∩ ρ(A)` of `ℂ` are read as subsets of `ℝ`. -/
theorem projection_spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (P : Set ℝ → (H →L[ℂ] H))
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hAP : A = spectralIntegral P (fun x => (x : ℂ))) :
    P {x : ℝ | (x : ℂ) ∈ spectrum A} = 1 ∧
      P {x : ℝ | (x : ℂ) ∈ resolventSet A} = 0 := by sorry

end TeschlQM.Spectral
