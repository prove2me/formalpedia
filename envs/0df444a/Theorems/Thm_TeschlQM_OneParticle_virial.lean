-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_virial
-- name    : TeschlQM.OneParticle.virial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:10:40.547962+00:00
-- url     : https://prove2.me/theorems/907579bd-37f4-4eab-88bc-3ea77590d4ee
-- title:
--   Theorem 10.3 — the virial theorem λ = −⟨ψ, H₀ψ⟩ = ½⟨ψ, Vψ⟩
-- statement:
--   Let $n \ge 1$ and let $U(s)\psi(x) = e^{-ns/2}\psi(e^{-s}x)$ be the dilation group on $L^2(\mathbb R^n)$. Suppose $V : \mathbb R^n \to \mathbb R$ is measurable with $U(-s) V U(s) = e^{-s} V$ for all $s \in \mathbb R$, and let $H = H_0 + V$ on $\mathfrak D(H_0) \cap \mathfrak D(V)$. Then any normalized eigenfunction $\psi$ of $H$ corresponding to an eigenvalue $\lambda$ satisfies
--   $$\lambda = -\langle \psi, H_0 \psi \rangle = \tfrac12 \langle \psi, V \psi \rangle .$$
--   In particular, every eigenvalue is real and negative.
--
--   The Coulomb potential $-\gamma/|x|$ is homogeneous of this kind, so the virial theorem shows that the hydrogen atom has no eigenvalues in $[0,\infty)$.
--
--   **Formalization Note.** Since $U(-s) V U(s)$ is multiplication by $x \mapsto V(e^s x)$, the hypothesis is stated as: for every $s$, $V(e^s x) = e^{-s} V(x)$ for almost every $x$. The eigenfunction $\psi$ lies in $\mathfrak D(H_0) \cap \mathfrak D(V)$ with $\|\psi\| = 1$ and $H_0\psi + V\psi = \lambda\psi$. "Negative" is $\operatorname{Im}\lambda = 0$ and $\operatorname{Re}\lambda < 0$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 223, Theorem 10.3

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian

namespace TeschlQM.OneParticle

open MeasureTheory
open scoped InnerProductSpace

/-- Teschl, Theorem 10.3 (virial theorem), p. 223. Suppose `H = H₀ + V` with
`U(-s) V U(s) = e^{-s} V`, where `U(s)ψ(x) = e^{-ns/2} ψ(e^{-s}x)` is the dilation group (10.8).
Then any normalized eigenfunction `ψ` corresponding to an eigenvalue `λ` satisfies
`λ = -⟨ψ, H₀ψ⟩ = ½⟨ψ, Vψ⟩` (10.13). In particular, all eigenvalues must be negative.

For the multiplication operator `V`, `U(-s) V U(s)` is multiplication by `x ↦ V(e^s x)`, so the
hypothesis is `V(e^s x) = e^{-s} V(x)` for a.e. `x`, for every `s ∈ ℝ`. `V` is measurable (2.21),
`H₀ + V` is the operator sum on `𝔇(H₀) ∩ 𝔇(V)`, and `n ≥ 1`. -/
theorem virial (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ) (hVm : Measurable V)
    (hV : ∀ s : ℝ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      V (Real.exp s • x) = Real.exp (-s) * V x)
    (lam : ℂ) (ψ : L2 n) (hψH₀ : ψ ∈ (freeHamiltonian n).domain)
    (hψV : ψ ∈ (multOp (fun x => (V x : ℂ))).domain) (hψ1 : ‖ψ‖ = 1)
    (heig : freeHamiltonian n ⟨ψ, hψH₀⟩ + multOp (fun x => (V x : ℂ)) ⟨ψ, hψV⟩ = lam • ψ) :
    lam = -⟪ψ, (freeHamiltonian n ⟨ψ, hψH₀⟩)⟫_ℂ ∧
      lam = (1 / 2 : ℂ) * ⟪ψ, (multOp (fun x => (V x : ℂ)) ⟨ψ, hψV⟩)⟫_ℂ ∧
      lam.im = 0 ∧ lam.re < 0 := by sorry

end TeschlQM.OneParticle
