-- Prove2me | Theorems.Thm_TeschlQM_Spectral_spectral_theorem
-- name    : TeschlQM.Spectral.spectral_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:31:11.594516+00:00
-- url     : https://prove2.me/theorems/c1bf4596-7644-4da0-b976-67ed3d060670
-- title:
--   Theorem 3.7 — Spectral theorem for unbounded self-adjoint operators
-- statement:
--   Let $\mathfrak H$ be a complex Hilbert space and let $A$ be a self-adjoint operator in $\mathfrak H$ (densely defined, with $A^* = A$, domains included). Then there is a unique projection-valued measure $P_A$ on the Borel sets of $\mathbb{R}$ such that
--   $$A = \int_{\mathbb{R}} \lambda\, dP_A(\lambda) \qquad (3.49),$$
--   that is, $A$ equals the spectral integral $P_A(f)$ of the function $f(\lambda) = \lambda$: $\mathfrak D(A) = \{\psi \mid \int \lambda^2\, d\mu_\psi(\lambda) < \infty\}$ and $\langle\psi, A\psi\rangle = \int \lambda\, d\mu_\psi(\lambda)$ on it, where $\mu_\psi$ are the spectral measures of $P_A$.
--
--   The theorem converts every self-adjoint operator into a multiplication by the identity function against a projection-valued measure; it is what gives meaning to $f(A) = P_A(f)$, to the unitary group $e^{-itA}$ and to the spectral projections $P_A(\Omega)$ used throughout quantum mechanics.
--
--   **Formalization Note.** $A$ is a `LinearPMap` `H →ₗ.[ℂ] H` and self-adjointness is Mathlib's `IsSelfAdjoint A` (which includes density of the domain). The equality in (3.49) is equality of `LinearPMap`s, domains included, with `spectralIntegral`. Existence and uniqueness are both asserted; uniqueness says any projection-valued measure $Q$ with $A = \int \lambda\, dQ(\lambda)$ agrees with $P_A$ on every Borel set. The only hypothesis is self-adjointness; the Hilbert space is not assumed separable (the result and the book's proof do not need it).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 96, Theorem 3.7

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 96, Theorem 3.7 (Spectral theorem). To every self-adjoint operator `A` there
corresponds a unique projection-valued measure `P_A` such that `A = ∫_ℝ λ dP_A(λ)` (3.49), the
equality being one of operators, domains included. Uniqueness is among projection-valued
measures, which are determined by their values on Borel sets. -/
theorem spectral_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ P : Set ℝ → (H →L[ℂ] H), TeschlQM.Shared.IsProjValuedMeasure P ∧
      A = spectralIntegral P (fun x => (x : ℂ)) ∧
      ∀ Q : Set ℝ → (H →L[ℂ] H), TeschlQM.Shared.IsProjValuedMeasure Q →
        A = spectralIntegral Q (fun x => (x : ℂ)) →
        ∀ Ω : Set ℝ, MeasurableSet Ω → Q Ω = P Ω := by sorry

end TeschlQM.Spectral
