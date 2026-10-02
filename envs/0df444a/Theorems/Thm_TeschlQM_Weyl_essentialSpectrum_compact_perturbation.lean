-- Prove2me | Theorems.Thm_TeschlQM_Weyl_essentialSpectrum_compact_perturbation
-- name    : TeschlQM.Weyl.essentialSpectrum_compact_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:18:59.106584+00:00
-- url     : https://prove2.me/theorems/674a4080-8f61-4a6c-b4eb-3218e1bf328a
-- title:
--   Lemma 6.18 — σ_ess(A) is the part of σ(A) invariant under compact perturbations
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$. For every compact self-adjoint $K \in \mathfrak C(\mathfrak H)$ the operator $A + K$ (with domain $\mathfrak D(A)$) has the same essential spectrum, $\sigma_{ess}(A + K) = \sigma_{ess}(A)$, and the essential spectrum is exactly the part of the spectrum invariant under such perturbations:
--   $$\sigma_{ess}(A) = \bigcap_{K \in \mathfrak C(\mathfrak H),\, K^* = K} \sigma(A + K).$$
--
--   This characterizes $\sigma_{ess}$ intrinsically: every point of the discrete spectrum can be removed by a suitable compact self-adjoint perturbation, and no point of the essential spectrum can.
--
--   **Formalization Note.** $K$ is a bounded operator `H →L[ℂ] H` with `IsCompactOperator K` and `IsSelfAdjoint K`; $A + K$ is Mathlib's `K +ᵥ A`, the operator $\psi \mapsto A\psi + K\psi$ on $\mathfrak D(A)$. The book's phrase "precisely the part which is invariant under compact perturbations" is rendered as the conjunction of the invariance $\sigma_{ess}(A+K) = \sigma_{ess}(A)$ (proved in the text just before the lemma) and the intersection formula (6.32).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 146, Lemma 6.18

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.18, p. 146. The essential spectrum of a self-adjoint operator `A` is precisely
the part which is invariant under compact perturbations: `σ_ess(A + K) = σ_ess(A)` for every
compact self-adjoint `K ∈ 𝔏(ℌ)`, and (6.32)
`σ_ess(A) = ⋂_{K ∈ ℭ(ℌ), K* = K} σ(A + K)`.
`A + K` is the operator `ψ ↦ Aψ + Kψ` on `𝔇(A)` (Mathlib's `K +ᵥ A`). -/
theorem essentialSpectrum_compact_perturbation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    (∀ K : H →L[ℂ] H, IsCompactOperator K → IsSelfAdjoint K →
        TeschlQM.Shared.essentialSpectrum ((K : H →ₗ[ℂ] H) +ᵥ A) = TeschlQM.Shared.essentialSpectrum A) ∧
      TeschlQM.Shared.essentialSpectrum A =
        ⋂ (K : H →L[ℂ] H) (_ : IsCompactOperator K) (_ : IsSelfAdjoint K),
          TeschlQM.Shared.spectrum ((K : H →ₗ[ℂ] H) +ᵥ A) := by sorry

end TeschlQM.Weyl
