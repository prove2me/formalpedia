-- Prove2me | Theorems.Thm_TeschlQM_Atomic_ims_localization
-- name    : TeschlQM.Atomic.ims_localization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:04:38.920699+00:00
-- url     : https://prove2.me/theorems/7fa859e4-36cc-4dec-b12c-ab1930f8fac2
-- title:
--   Lemma 11.3 — IMS localization formula
-- statement:
--   Suppose $\varphi_j \in C^\infty(\mathbb R^n)$, $1 \le j \le m$, are real-valued with
--   $$\sum_{j=1}^m \varphi_j(x)^2 = 1, \qquad x \in \mathbb R^n.$$
--   Then for $\psi \in H^2(\mathbb R^n)$
--   $$\Delta\psi = \sum_{j=1}^m \big(\varphi_j \Delta(\varphi_j \psi) + |\partial\varphi_j|^2 \psi\big).$$
--
--   The formula localizes the kinetic energy with respect to a quadratic partition of unity at the cost of the error term $\sum_j |\partial\varphi_j|^2$; it is the tool that splits the $N$-electron Hamiltonian into pieces in which one electron is far from the nucleus.
--
--   **Formalization Note.** Since the $\varphi_j$ are only assumed smooth, the terms on the right-hand side are distributions, and the identity is stated in the sense of distributions: for every $\chi \in C_0^\infty(\mathbb R^n; \mathbb C)$,
--   $$\int (\Delta\psi)\,\chi\,d^nx = \sum_{j=1}^m \Big( \int \varphi_j \psi\, \Delta(\varphi_j \chi)\,d^nx + \int |\partial\varphi_j|^2 \psi\, \chi\,d^nx \Big),$$
--   with $\Delta\psi = -H_0\psi \in L^2$ (`freeHamiltonian`, Fourier-defined). $|\partial\varphi_j(x)|$ is the norm of `fderiv ℝ (φ j) x` (the length of the gradient) and $\Delta$ on smooth functions is Mathlib's Laplacian (trace of the second derivative). All integrands are integrable (an $L^2$ function times a bounded compactly supported one), so no integral is a junk value.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 243, Lemma 11.3

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian

namespace TeschlQM.Atomic

open MeasureTheory
open scoped ContDiff

/-- Teschl, Lemma 11.3 (IMS localization formula), p. 243. Suppose `φ_j ∈ C^∞(ℝⁿ)`, `1 ≤ j ≤ m`,
satisfy `∑_{j=1}^m φ_j(x)² = 1` for all `x ∈ ℝⁿ` (11.12). Then for `ψ ∈ H²(ℝⁿ)`
`Δψ = ∑_{j=1}^m (φ_j Δ(φ_j ψ) + |∂φ_j|² ψ)` (11.13).
Since the `φ_j` are only assumed smooth, the terms on the right are distributions, and (11.13) is
stated as an identity of distributions: tested against every `χ ∈ C₀^∞(ℝⁿ)`,
`⟨Δψ, χ⟩ = ∑_j (⟨φ_j ψ, Δ(φ_j χ)⟩ + ⟨|∂φ_j|² ψ, χ⟩)`, where `Δψ = -H₀ψ ∈ L²` and
`⟨f, χ⟩ = ∫ f χ dⁿx`. Here `|∂φ_j(x)|` is the norm of the derivative of `φ_j` at `x` (the length of
the gradient) and `Δ` on smooth functions is Mathlib's Laplacian `Laplacian.laplacian` (the trace of the second derivative). -/
theorem ims_localization {n m : ℕ} (φ : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hsum : ∀ x, ∑ j, φ j x ^ 2 = 1)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hψ : ψ ∈ (freeHamiltonian (Fin n)).domain)
    (χ : EuclideanSpace ℝ (Fin n) → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∫ x, -((freeHamiltonian (Fin n) ⟨ψ, hψ⟩ : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin n) → ℂ) x * χ x =
      ∑ j, ((∫ x, ((φ j x : ℝ) : ℂ) * (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x *
              Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => ((φ j y : ℝ) : ℂ) * χ y) x) +
            ∫ x, ((‖fderiv ℝ (φ j) x‖ ^ 2 : ℝ) : ℂ) * (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x * χ x) := by sorry

end TeschlQM.Atomic
