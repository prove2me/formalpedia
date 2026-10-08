-- Prove2me | Theorems.Thm_TeschlQM_MinMax_inf_sup_spectrum
-- name    : TeschlQM.MinMax.inf_sup_spectrum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:28:15.541012+00:00
-- url     : https://prove2.me/theorems/ba9e50e9-6fd7-45a1-8e67-71d1c5003509
-- title:
--   Theorem 2.19 — inf σ(A) and sup σ(A) as extremes of ⟨ψ, Aψ⟩ over unit vectors
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$ with domain $\mathfrak D(A)$ and spectrum $\sigma(A) \subseteq \mathbb R$. Then
--   $$\inf \sigma(A) = \inf_{\psi \in \mathfrak D(A),\ \|\psi\| = 1} \langle \psi, A\psi \rangle \qquad\text{and}\qquad \sup \sigma(A) = \sup_{\psi \in \mathfrak D(A),\ \|\psi\| = 1} \langle \psi, A\psi \rangle .$$
--
--   The bottom of the spectrum is thus the infimum of the expectation values of $A$; it is the case $n = 1$ of the min-max principle and the reason why any normalized trial vector gives an upper bound for the lowest eigenvalue.
--
--   **Formalization Note.** Both sides are in the extended reals `EReal`, so either side may be $\pm\infty$ (for an operator unbounded below or above; for $\mathfrak H = \{0\}$ both infima are $+\infty$ and both suprema $-\infty$). Since the spectrum of a self-adjoint operator is real, $\sigma(A)$ enters as the set of real $x$ with $x \in \sigma(A)$, the resolvent spectrum of p. 73; $\langle\psi, A\psi\rangle$ enters through its real part. The operator is a `LinearPMap` and self-adjointness is Mathlib's `IsSelfAdjoint`, which includes a dense domain.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 77, Theorem 2.19

import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, Theorem 2.19, p. 77, (2.90) and (2.91): for a self-adjoint `A`,
`inf σ(A) = inf_{ψ ∈ 𝔇(A), ‖ψ‖ = 1} ⟨ψ, Aψ⟩` and `sup σ(A) = sup_{ψ ∈ 𝔇(A), ‖ψ‖ = 1} ⟨ψ, Aψ⟩`,
in `EReal` (either side may be `±∞`; both are `+∞`/`−∞` when `ℌ = {0}`).
The spectrum of a self-adjoint operator is real, so `σ(A)` is taken as the set of real `x`
with `x ∈ σ(A)`. -/
theorem inf_sup_spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) =
        ⨅ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) ∧
      sSup ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ spectrum A}) =
        ⨆ (ψ : A.domain) (_ : ‖(ψ : H)‖ = 1), ((⟪(ψ : H), A ψ⟫_ℂ).re : EReal) := by sorry

end TeschlQM.MinMax
