-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_iff_spectrum_real
-- name    : TeschlQM.SelfAdjoint.selfAdjoint_iff_spectrum_real
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:22:13.405101+00:00
-- url     : https://prove2.me/theorems/700e3944-83df-411b-9ad7-9c08f42106a3
-- title:
--   Theorem 2.18 — self-adjoint iff σ(A) ⊆ ℝ; resolvent bounds
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space $\mathfrak{H}$ and $E \in \mathbb{R}$. Then
--
--   1. $A$ is self-adjoint if and only if $\sigma(A) \subseteq \mathbb{R}$;
--   2. $A$ is self-adjoint with $A - E \ge 0$ if and only if $\sigma(A) \subseteq [E, \infty)$;
--   3. if $A$ is self-adjoint, then for $z \in \mathbb{C}\setminus\mathbb{R}$
--   $$\|R_A(z)\| \le |\operatorname{Im}(z)|^{-1};$$
--   4. if $A$ is self-adjoint and $A - E \ge 0$, then $\|R_A(\lambda)\| \le |\lambda - E|^{-1}$ for real $\lambda < E$.
--
--   Here $A - E \ge 0$ means $\langle \psi, (A - E)\psi \rangle \ge 0$ for all $\psi \in \mathfrak{D}(A)$, and $\sigma(A)$, $R_A(z)$ are the spectrum and resolvent of Section 2.4.
--
--   **Formalization Note.** $\sigma(A)$ is `opSpectrum A`, the complement of the set of $z$ for which $A - z$ has a bounded everywhere-defined two-sided inverse (not Mathlib's Banach-algebra `spectrum`). $A - E \ge 0$ is written $E\|\psi\|^2 \le \operatorname{Re}\langle\psi, A\psi\rangle$. The norm bounds quantify over every bounded $R$ that is the resolvent at the given point; by parts 1–2 such an $R$ exists, and it is unique.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 77, Theorem 2.18

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.SelfAdjoint

open scoped InnerProductSpace

/-- Teschl, Theorem 2.18 (p. 77): for symmetric `A`,
(i) `A` is self-adjoint iff `σ(A) ⊆ ℝ`;
(ii) for `E ∈ ℝ`, `A` is self-adjoint with `A - E ≥ 0` iff `σ(A) ⊆ [E, ∞)`;
(iii) for self-adjoint `A` and `z ∉ ℝ`, `‖R_A(z)‖ ≤ |Im z|⁻¹`;
(iv) for self-adjoint `A` with `A - E ≥ 0` and real `λ < E`, `‖R_A(λ)‖ ≤ |λ - E|⁻¹`.
`A - E ≥ 0` means `E‖ψ‖² ≤ Re⟨ψ, Aψ⟩` for `ψ ∈ 𝔇(A)` (the form is real for symmetric `A`). -/
theorem selfAdjoint_iff_spectrum_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (IsSelfAdjoint A ↔ TeschlQM.Shared.spectrum A ⊆ {z : ℂ | z.im = 0}) ∧
    (∀ E : ℝ, (IsSelfAdjoint A ∧ ∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) ↔
      TeschlQM.Shared.spectrum A ⊆ {z : ℂ | z.im = 0 ∧ E ≤ z.re}) ∧
    (IsSelfAdjoint A → ∀ z : ℂ, z.im ≠ 0 → ∀ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A z R →
      ‖R‖ ≤ |z.im|⁻¹) ∧
    (∀ E : ℝ, IsSelfAdjoint A → (∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) →
      ∀ l : ℝ, l < E → ∀ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A (l : ℂ) R → ‖R‖ ≤ |l - E|⁻¹) := by sorry

end TeschlQM.SelfAdjoint
