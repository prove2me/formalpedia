-- Prove2me | Theorems.Thm_TeschlQM_Weyl_weyl_criterion
-- name    : TeschlQM.Weyl.weyl_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:14:09.943142+00:00
-- url     : https://prove2.me/theorems/2e74ffdb-7f8d-44a0-8ba1-63dcd427cd63
-- title:
--   Lemma 6.17 — Weyl criterion
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$ and $z \in \mathbb C$. Then $z$ lies in the essential spectrum $\sigma_{ess}(A)$ if and only if there is a sequence $\psi_n \in \mathfrak D(A)$ with
--   $$\|\psi_n\| = 1, \qquad \psi_n \rightharpoonup 0, \qquad \|(A - z)\psi_n\| \to 0,$$
--   that is, a singular Weyl sequence. Moreover, if $z \in \sigma_{ess}(A)$, the sequence can be chosen orthonormal.
--
--   The Weyl criterion turns membership in the essential spectrum into the existence of approximate eigenvectors that escape weakly to zero; it is the tool behind every stability result for $\sigma_{ess}$.
--
--   **Formalization Note.** $A$ is a `LinearPMap` with `IsSelfAdjoint A` (which implies a dense domain). $\sigma_{ess}$ is the PVM-free definition $\sigma(A) \setminus \sigma_d(A)$ of p. 145. Weak convergence is $\langle\varphi,\psi_n\rangle \to 0$ for all $\varphi$. The Hilbert space is complete but not assumed separable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 145, Lemma 6.17

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Weyl_IsSingularWeylSequence

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.17 (Weyl criterion), p. 145. A point `z` is in the essential spectrum of a
self-adjoint operator `A` if and only if there is a sequence `ψₙ ∈ 𝔇(A)` with `‖ψₙ‖ = 1`,
`ψₙ ⇀ 0` weakly and `‖(A - z)ψₙ‖ → 0` (a singular Weyl sequence). Moreover, the sequence can be
chosen orthonormal. -/
theorem weyl_criterion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) :
    (z ∈ TeschlQM.Shared.essentialSpectrum A ↔ ∃ ψ : ℕ → A.domain, IsSingularWeylSequence A z ψ) ∧
      (z ∈ TeschlQM.Shared.essentialSpectrum A → ∃ ψ : ℕ → A.domain,
        IsSingularWeylSequence A z ψ ∧ Orthonormal ℂ (fun n => (ψ n : H))) := by sorry

end TeschlQM.Weyl
