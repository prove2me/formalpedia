-- Prove2me | Theorems.Thm_TeschlQM_Weyl_weyl
-- name    : TeschlQM.Weyl.weyl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:30:44.824681+00:00
-- url     : https://prove2.me/theorems/295972b2-4780-49dc-af4d-9c3bd798e3ba
-- title:
--   Theorem 6.19 — Weyl's theorem: a compact resolvent difference preserves σ_ess
-- statement:
--   Let $A$ and $B$ be self-adjoint operators in a complex Hilbert space $\mathfrak H$. If
--   $$R_A(z) - R_B(z) \in \mathfrak C(\mathfrak H)$$
--   for one $z \in \rho(A) \cap \rho(B)$, then
--   $$\sigma_{ess}(A) = \sigma_{ess}(B).$$
--
--   Weyl's theorem is the basic tool for locating the essential spectrum of Schrödinger operators: a perturbation that is small in the sense of a compact resolvent difference (for instance a relatively compact perturbation) leaves the essential spectrum unchanged.
--
--   **Formalization Note.** $A$, $B$ are `LinearPMap`s with `IsSelfAdjoint`. The resolvent $R_A(z)$ is the bounded two-sided inverse of $A - z$ (p. 73, `IsResolventAt`), and "for one $z$" is an existential over $z$ and the two resolvents. $\sigma_{ess}$ is $\sigma \setminus \sigma_d$ with $\sigma_d$ the isolated eigenvalues of finite multiplicity (p. 145). Compactness is Mathlib's `IsCompactOperator`. The Hilbert space is not assumed separable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 146, Theorem 6.19

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum

namespace TeschlQM.Weyl

/-- Teschl, Theorem 6.19 (Weyl), p. 146. Suppose `A` and `B` are self-adjoint operators. If
`R_A(z) - R_B(z) ∈ ℭ(ℌ)` (6.33) for one `z ∈ ρ(A) ∩ ρ(B)`, then `σ_ess(A) = σ_ess(B)` (6.34).
"For one `z ∈ ρ(A) ∩ ρ(B)`" is the existence of `z` together with the resolvents `R_A(z)`,
`R_B(z)` of `A` and `B` at `z`. -/
theorem weyl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : ∃ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA ∧ TeschlQM.Shared.IsResolventAt B z RB ∧
      IsCompactOperator (RA - RB)) :
    TeschlQM.Shared.essentialSpectrum A = TeschlQM.Shared.essentialSpectrum B := by sorry

end TeschlQM.Weyl
