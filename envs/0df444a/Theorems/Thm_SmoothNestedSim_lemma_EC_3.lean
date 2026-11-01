-- Prove2me | Theorems.Thm_SmoothNestedSim_lemma_EC_3
-- name    : SmoothNestedSim.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:03.330158+00:00
-- url     : https://prove2.me/theorems/6b2f1c8b-8f3e-4812-bda4-7fa252f856e8
-- title:
--   Lemma EC.3: tail bound for the sub-Gaussian empirical process over $\mathcal N_\Psi(\Omega)$
-- statement:
--   Let $\nu>0$, $\ell>0$, $\Omega\subseteq\mathbb R^d$ bounded and convex, and $\sigma^2\ge0$. There are constants $C_1,C_2>0$ and $t_0$ such that for every $n\ge1$, all $\mathbf x_1,\dots,\mathbf x_n\in\Omega$, all independent zero-mean $\mathrm{subG}(\sigma^2)$ variables $\epsilon_1,\dots,\epsilon_n$ and all $t\ge t_0$,
--
--   $$
--   \Pr\Biggl(\sup_{g\in\mathcal N_\Psi(\Omega),\ \|g\|_n>0}\ \frac{\bigl|\frac1n\sum_{j=1}^n\epsilon_jg(\mathbf x_j)\bigr|}{\|g\|_n^{1-\frac{d}{2\nu+d}}\ \|g\|_{\mathcal N_\Psi(\Omega)}^{\frac{d}{2\nu+d}}}\ \ge\ t\,n^{-1/2}\Biggr)\le C_1\exp(-C_2t^2),
--   $$
--
--   where $\|g\|_n=(n^{-1}\sum_i g^2(\mathbf x_i))^{1/2}$ is the empirical semi-norm.
--
--   This modulus of continuity of the weighted empirical process (Lemma A.1 in Tuo et al. 2020, after van de Geer 2000) is the probabilistic input of Proposition 2.
--
--   **Formalization Note** The independent variables are the coordinates under the product law $\bigotimes_j\xi_j$. The supremum is taken in $[0,\infty]$ and the probability of a non-measurable event is its outer measure.
--
--   Differences from the source:
--   - reading: there exist C₁, C₂ such that for t large enough (x_j, the variance proxy and the dependence of the constants left implicit) → for every σ² there are C₁, C₂ > 0 and t₀, chosen before n, the design points x₁,…,xₙ ∈ Ω and the laws of the εⱼ, such that the bound holds for all t ≥ t₀; reason: this is how the proof of Proposition 2 uses the lemma (on the realised design, with ε̄ᵢ ∼ subG(σ²/m)); it is the uniform reading, the stronger one
--   - encoding: sup over g ∈ N_Ψ(Ω) → sup over g ∈ N_Ψ(Ω) with ‖g‖ₙ > 0, taken in [0, ∞]; reason: for ‖g‖ₙ = 0 the ratio is 0/0; an unbounded supremum is +∞ instead of a junk real value
--   - encoding: n ≥ 1 sample points → 0 < n; reason: the empirical semi-norm and n^{-1/2} need n ≥ 1
--   - encoding: zero-mean subG(σ²): 𝔼[e^{t(Z−𝔼Z)}] ≤ e^{σ²t²/2} and 𝔼Z = 0 (Definition 1, p.15) → HasSubgaussianMGF id σ² (𝔼[e^{tZ}] ≤ e^{σ²t²/2}, exponential moments integrable); reason: for a zero-mean Z the two inequalities coincide, and the Mathlib predicate forces 𝔼Z = 0 (proved in the verification file)
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, Lemma EC.3, p.ec11 (PDF p.57)

import Mathlib
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_rkhsNorm
import Definitions.Def_SmoothNestedSim_empiricalNorm

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SmoothNestedSim

/-- **Lemma EC.3** (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6,
Lemma EC.3, p.ec11 = PDF p.57, citing Lemma A.1 in Tuo et al. 2020): "Let `Ω` be a bounded
convex subset of `ℝ^d` and `{ϵ₁, …, ϵₙ}` be independent, zero-mean sub-Gaussian random
variables. Then, there exist positive constants `C₁` and `C₂` such that for all `t` large
enough,
`Pr( sup_{g∈N_Ψ(Ω)} |(1/n) Σⱼ ϵⱼ g(xⱼ)| / (‖g‖_n^{1−d/(2ν+d)} ‖g‖_{N_Ψ(Ω)}^{d/(2ν+d)}) ≥ t n^{−1/2} )
≤ C₁ exp(−C₂ t²)`, where `‖g‖_n` denotes the empirical semi-norm of `g`."

Read uniformly: for `ν, ℓ > 0`, a bounded convex `Ω` and a variance proxy `σ²`, there are
`C₁, C₂ > 0` and `t₀` such that for every `n ≥ 1`, every `x₁, …, xₙ ∈ Ω`, every family of
independent zero-mean `subG(σ²)` variables `ϵ₁, …, ϵₙ` and every `t ≥ t₀` the displayed bound
holds.

**Formalization Note.** The constants are chosen before `n`, the design points and the noise
laws, as the use in the proof of Proposition 2 (p.ec12, with the design realised and
`ϵ̄ᵢ ∼ subG(σ²/m)`) requires. Independent `ϵⱼ ∼ ξⱼ` are the coordinates under the product law
`⊗ⱼ ξⱼ`; zero-mean `subG(σ²)` is `HasSubgaussianMGF id σ²`. The supremum is over `g ∈ N_Ψ(Ω)`
with `‖g‖_n > 0` (otherwise the ratio is `0/0`) and is taken in `[0, ∞]`; the probability of a
possibly non-measurable event is its outer measure. -/
theorem lemma_EC_3 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩb : Bornology.IsBounded Ω) (hΩc : Convex ℝ Ω)
    (σsq : ℝ≥0) :
    ∃ C₁ C₂ t₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n : ℕ), 0 < n → ∀ x : Fin n → EuclideanSpace ℝ (Fin d), (∀ j, x j ∈ Ω) →
      ∀ ξ : Fin n → ProbabilityMeasure ℝ, (∀ j, HasSubgaussianMGF id σsq (ξ j : Measure ℝ)) →
      ∀ t : ℝ, t₀ ≤ t →
        Measure.pi (fun j => (ξ j : Measure ℝ))
          {ε : Fin n → ℝ | ENNReal.ofReal (t * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
            ⨆ (g : EuclideanSpace ℝ (Fin d) → ℝ)
              (_ : g ∈ RKHS (maternKernel ν ℓ) Ω ∧ 0 < empiricalNorm x g),
              ENNReal.ofReal (|(1 / (n : ℝ)) * ∑ j, ε j * g (x j)| /
                (empiricalNorm x g ^ (1 - (d : ℝ) / (2 * ν + d)) *
                  rkhsNorm (maternKernel ν ℓ) Ω g ^ ((d : ℝ) / (2 * ν + d))))} ≤
          ENNReal.ofReal (C₁ * Real.exp (-C₂ * t ^ 2)) := by sorry

end SmoothNestedSim
