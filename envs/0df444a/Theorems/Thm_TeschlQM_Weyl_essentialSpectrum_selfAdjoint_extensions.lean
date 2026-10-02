-- Prove2me | Theorems.Thm_TeschlQM_Weyl_essentialSpectrum_selfAdjoint_extensions
-- name    : TeschlQM.Weyl.essentialSpectrum_selfAdjoint_extensions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:35:49.332757+00:00
-- url     : https://prove2.me/theorems/7e9d3e74-05f7-44bb-bac4-8f458d5cb771
-- title:
--   Theorem 6.20 — self-adjoint extensions with equal finite defect indices share σ_ess
-- statement:
--   Let $A$ be a symmetric operator in a complex Hilbert space $\mathfrak H$ with equal finite defect indices, $d_+(A) = d_-(A) < \infty$. Then all self-adjoint extensions of $A$ have the same essential spectrum: if $A_1 \supseteq A$ and $A_2 \supseteq A$ are self-adjoint, then
--   $$\sigma_{ess}(A_1) = \sigma_{ess}(A_2).$$
--
--   In applications (Sturm–Liouville operators with limit circle endpoints, point interactions) the choice of boundary condition is therefore irrelevant for the essential spectrum.
--
--   **Formalization Note.** $A \subseteq A_j$ is the `LinearPMap` order `A ≤ A_j`. Symmetric includes density of $\mathfrak D(A)$. The defect spaces are $\operatorname{Ran}(A \pm i)^\perp$ and "equal finite" means both are finite dimensional with equal `finrank`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 147, Theorem 6.20

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Weyl_defectSpace

namespace TeschlQM.Weyl

/-- Teschl, Theorem 6.20, p. 147. Suppose `A` is symmetric with equal finite defect indices
`d₊(A) = d₋(A) < ∞`. Then all self-adjoint extensions of `A` have the same essential spectrum:
for any two self-adjoint `A₁ ⊇ A` and `A₂ ⊇ A`, `σ_ess(A₁) = σ_ess(A₂)`. -/
theorem essentialSpectrum_selfAdjoint_extensions {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (hdef : HasEqualFiniteDefectIndices A) (A₁ A₂ : H →ₗ.[ℂ] H) (h₁ : A ≤ A₁) (h₂ : A ≤ A₂)
    (hs₁ : IsSelfAdjoint A₁) (hs₂ : IsSelfAdjoint A₂) :
    TeschlQM.Shared.essentialSpectrum A₁ = TeschlQM.Shared.essentialSpectrum A₂ := by sorry

end TeschlQM.Weyl
