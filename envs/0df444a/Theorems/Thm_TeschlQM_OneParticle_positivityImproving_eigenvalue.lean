-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_positivityImproving_eigenvalue
-- name    : TeschlQM.OneParticle.positivityImproving_eigenvalue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:29:18.554831+00:00
-- url     : https://prove2.me/theorems/476824d2-0f81-411a-b2af-9fd0bbc836de
-- title:
--   Theorem 10.11 — for a positivity improving operator, ‖A‖ is a simple eigenvalue with positive eigenfunction
-- statement:
--   Let $A$ be a bounded self-adjoint operator on $L^2(\mathbb R^n)$ which is positivity improving (it maps every positive function to a strictly positive one) and real (it maps real functions to real functions). If $\|A\|$ is an eigenvalue of $A$, then it is simple and the corresponding eigenfunction is strictly positive:
--   $$\dim \operatorname{Ker}(A - \|A\|) = 1, \qquad \operatorname{Ker}(A - \|A\|) \ni \psi \text{ with } \psi > 0 \text{ a.e.}$$
--
--   This is an infinite-dimensional Perron–Frobenius theorem; applied to resolvents it yields nondegeneracy of ground states.
--
--   **Formalization Note.** "Self-adjoint" is Mathlib's `IsSelfAdjoint` for `L2 n →L[ℂ] L2 n`, "$\|A\|$ is an eigenvalue" is the existence of $\psi \ne 0$ with $A\psi = \|A\|\psi$, and "simple" is `Module.finrank ℂ (Module.End.eigenspace A ‖A‖) = 1` (an infinite-dimensional eigenspace would have `finrank` $0$). Positivity uses `ComplexOrder` pointwise almost everywhere.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 236, Theorem 10.11

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_positivity

namespace TeschlQM.OneParticle

/-- Teschl, Theorem 10.11, p. 236. Suppose `A ∈ 𝔏(L²(ℝⁿ))` is a self-adjoint, positivity improving
and real (i.e., it maps real functions to real functions) operator. If `‖A‖` is an eigenvalue,
then it is simple and the corresponding eigenfunction is strictly positive: the eigenspace of
`‖A‖` is one-dimensional and contains a strictly positive function. -/
theorem positivityImproving_eigenvalue (n : ℕ) (A : L2 n →L[ℂ] L2 n) (hA : IsSelfAdjoint A)
    (hpos : IsPositivityImproving A) (hreal : IsRealOperator A)
    (heig : ∃ ψ : L2 n, ψ ≠ 0 ∧ A ψ = (‖A‖ : ℂ) • ψ) :
    Module.finrank ℂ (Module.End.eigenspace (A : Module.End ℂ (L2 n)) (‖A‖ : ℂ)) = 1 ∧
      ∃ ψ : L2 n, A ψ = (‖A‖ : ℂ) • ψ ∧ IsStrictlyPositive ψ := by sorry

end TeschlQM.OneParticle
