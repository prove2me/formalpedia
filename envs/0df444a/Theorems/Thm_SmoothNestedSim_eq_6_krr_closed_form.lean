-- Prove2me | Theorems.Thm_SmoothNestedSim_eq_6_krr_closed_form
-- name    : SmoothNestedSim.eq_6_krr_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:30.878664+00:00
-- url     : https://prove2.me/theorems/8cdd0a39-ea0b-483c-9f8f-3b116432a663
-- title:
--   (6): the closed form $\mathbf r(\mathbf x)^\top(\mathbf R+n\lambda\mathbf I)^{-1}\bar{\mathbf y}$ is the unique solution of the KRR problem (5)
-- statement:
--   Let $\nu>0$, $\ell>0$, $\Omega\subseteq\mathbb R^d$ bounded and convex, $n\ge1$, $\mathbf x_1,\dots,\mathbf x_n\in\Omega$ (not necessarily distinct), $\bar{\mathbf y}\in\mathbb R^n$ and $\lambda>0$. Let $\hat f(\mathbf x)=\mathbf r(\mathbf x)^\top(\mathbf R+n\lambda\mathbf I)^{-1}\bar{\mathbf y}$ with $\mathbf r(\mathbf x)=(\Psi(\mathbf x-\mathbf x_1),\dots,\Psi(\mathbf x-\mathbf x_n))^\top$ and $\mathbf R=(\Psi(\mathbf x_i-\mathbf x_j))_{i,j}$, $\Psi$ the Matérn function. Then
--
--   1. $\hat f\in\mathcal N_\Psi(\Omega)$;
--   2. $\hat f$ minimizes $\displaystyle \frac1n\sum_{i=1}^n(\bar y_i-g(\mathbf x_i))^2+\lambda\|g\|^2_{\mathcal N_\Psi(\Omega)}$ over $g\in\mathcal N_\Psi(\Omega)$;
--   3. every minimizer $g\in\mathcal N_\Psi(\Omega)$ coincides with $\hat f$ on $\Omega$.
--
--   That is, $\hat f=\arg\min_{g\in\mathcal N_\Psi(\Omega)}(\cdots)$, the identity (6) through which the paper computes the KRR estimator and on which the proofs of Propositions 1 and 2 rest.
--
--   Differences from the source:
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - encoding: f̂ = argmin (a unique element of N_Ψ(Ω)) → f̂ ∈ N_Ψ(Ω), f̂ minimizes, and every minimizer equals f̂ on Ω; reason: elements of N_Ψ(Ω) are functions on Ω, so uniqueness is uniqueness on Ω
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.2, (5)–(6), p.12

import Mathlib
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_krrEstimator
import Definitions.Def_SmoothNestedSim_krrObjective

namespace SmoothNestedSim

/-- **(6): the closed form is the unique solution of the KRR problem (5)** (Wang, Wang, Zhang,
*Smooth Nested Simulation*, arXiv:2201.02958v6, §3.2, (5)–(6), p.12): "The optimal solution to
(5) is `f̂ := argmin_{g∈N_Ψ(Ω)} ( (1/n) Σᵢ (ȳᵢ − g(xᵢ))² + λ‖g‖²_{N_Ψ(Ω)} ) = r(x)ᵀ(R + nλI)⁻¹ȳ`".

For `ν > 0`, `ℓ > 0`, a bounded convex `Ω ⊂ ℝ^d`, `n ≥ 1` points `x₁, …, xₙ ∈ Ω` (not
necessarily distinct), any `ȳ ∈ ℝⁿ` and `λ > 0`: the closed form `f̂ = r(·)ᵀ(R + nλI)⁻¹ȳ`
lies in the Matérn RKHS `N_Ψ(Ω)`, minimizes the objective (5) over `N_Ψ(Ω)`, and every other
minimizer in `N_Ψ(Ω)` coincides with `f̂` on `Ω`.

**Formalization Note.** Members of `N_Ψ(Ω)` are functions on `ℝ^d` of which only the values on
`Ω` matter, so uniqueness of the minimizer is uniqueness on `Ω`. -/
theorem eq_6_krr_closed_form {d n : ℕ} (hn : 0 < n) (ν ℓ lam : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (hlam : 0 < lam) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩb : Bornology.IsBounded Ω)
    (hΩc : Convex ℝ Ω) (x : Fin n → EuclideanSpace ℝ (Fin d)) (hx : ∀ i, x i ∈ Ω)
    (ybar : Fin n → ℝ) :
    krrEstimator ν ℓ lam x ybar ∈ RKHS (maternKernel ν ℓ) Ω ∧
      (∀ g ∈ RKHS (maternKernel ν ℓ) Ω,
        krrObjective ν ℓ lam Ω x ybar (krrEstimator ν ℓ lam x ybar) ≤
          krrObjective ν ℓ lam Ω x ybar g) ∧
      (∀ g ∈ RKHS (maternKernel ν ℓ) Ω,
        krrObjective ν ℓ lam Ω x ybar g ≤
            krrObjective ν ℓ lam Ω x ybar (krrEstimator ν ℓ lam x ybar) →
          ∀ z ∈ Ω, g z = krrEstimator ν ℓ lam x ybar z) := by sorry

end SmoothNestedSim
