-- Prove2me | Theorems.Thm_TeschlQM_Free_free_selfAdjoint_spectrum
-- name    : TeschlQM.Free.free_selfAdjoint_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:58:55.983397+00:00
-- url     : https://prove2.me/theorems/2a4df184-d244-4ef4-870e-4fb07d202c4e
-- title:
--   Theorem 7.8 — H₀ is self-adjoint, σ(H₀) = σ_ac(H₀) = [0, ∞), σ_sc(H₀) = σ_pp(H₀) = ∅
-- statement:
--   Let $n \ge 1$ and let $H_0 = -\Delta$ be the free Schrödinger operator on $L^2(\mathbb R^n)$ with domain $H^2(\mathbb R^n)$. Then $H_0$ is self-adjoint and its spectrum is characterized by
--   $$\sigma(H_0) = \sigma_{ac}(H_0) = [0,\infty), \qquad \sigma_{sc}(H_0) = \sigma_{pp}(H_0) = \emptyset .$$
--   Concretely: $H_0 = H_0^*$; the spectrum $\sigma(H_0) = \mathbb C \setminus \rho(H_0)$ is $[0,\infty)$; and for every $\psi \in L^2(\mathbb R^n)$ the spectral measure $\mu_\psi$ of $H_0$, the finite Borel measure on $\mathbb R$ with
--   $$\langle \psi, R_{H_0}(z)\psi\rangle = \int_{\mathbb R} \frac{1}{\lambda - z}\, d\mu_\psi(\lambda) \qquad (z \in \mathbb C \setminus \mathbb R),$$
--   is absolutely continuous with respect to Lebesgue measure.
--
--   This is the spectral analysis of the simplest quantum Hamiltonian: the free particle has no bound states and purely absolutely continuous spectrum filling the positive half-line.
--
--   **Formalization Note.** `freeHamiltonian n` is $H_0$ (see its definition). Self-adjointness is Mathlib's `IsSelfAdjoint` for `LinearPMap`, which includes density of the domain. $\sigma(H_0)$ is the resolvent spectrum of p. 73 (`TeschlQM.Free.spectrum`), not an essential range, and $[0,\infty)$ is the image of `Set.Ici 0` in $\mathbb C$. The spectral-type part is stated as the book's proof reduces it ("it suffices to show that $d\mu_\psi$ is purely absolutely continuous for every $\psi$"): for every $\psi$ there is a finite measure $\mu \ll$ Lebesgue whose Borel transform is $\langle\psi, R\psi\rangle$ for every resolvent $R = R_{H_0}(z)$, $z \notin \mathbb R$. A finite measure is determined by its Borel transform (Stieltjes inversion), so $\mu = \mu_\psi$; with $\sigma(H_0) = [0,\infty)$ this is equivalent to $\mathfrak H_{ac} = L^2$, i.e. to (7.25). No projection-valued measure is taken as data. The hypothesis $n \ge 1$ is implicit in the book: for $n = 0$, $H_0 = 0$ on $\mathbb C$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 168, Theorem 7.8

import Mathlib
import Definitions.Def_TeschlQM_Free_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Free

open MeasureTheory
open scoped InnerProductSpace

/-- Teschl, Theorem 7.8, p. 168: the free Schrödinger operator `H₀` is self-adjoint and
`σ(H₀) = σ_ac(H₀) = [0, ∞)`, `σ_sc(H₀) = σ_pp(H₀) = ∅` (7.25).

The spectral-type part is stated as the book's proof reduces it (p. 168): for every `ψ` the
spectral measure `μ_ψ` of `H₀` is purely absolutely continuous. `μ_ψ` is characterized
intrinsically, as the finite Borel measure whose Borel transform is `⟨ψ, R_{H₀}(z) ψ⟩` for every
nonreal `z` (Theorem 3.6 / (3.20)), with `R_{H₀}(z)` the resolvent of p. 73; a finite measure is
determined by its Borel transform, so `μ` is `μ_ψ`. With `σ(H₀) = [0, ∞)` this gives
`ℌ_ac = ℌ`, i.e. `σ_ac(H₀) = [0, ∞)` and `σ_sc(H₀) = σ_pp(H₀) = ∅`. `σ(H₀)` is the resolvent
spectrum of p. 73, not an essential range. `n ≥ 1`: for `n = 0`, `H₀ = 0` on `ℂ`. -/
theorem free_selfAdjoint_spectrum (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (freeHamiltonian n) ∧
      TeschlQM.Shared.spectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      ∀ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ ≪ volume ∧
          ∀ z : ℂ, z.im ≠ 0 →
            ∀ R : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
                Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
              TeschlQM.Shared.IsResolventAt (freeHamiltonian n) z R →
                ⟪ψ, R ψ⟫_ℂ = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ := by sorry

end TeschlQM.Free
