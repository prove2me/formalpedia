-- Prove2me | Theorems.Thm_PolySampIso_proposition_1
-- name    : PolySampIso.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:08.372965+00:00
-- url     : https://prove2.me/theorems/34e1f7f0-e11c-4e36-a7dd-af611a049d97
-- title:
--   Proposition 1, p.9 — χ² contraction of the LLT proximal sampler ([GST26, Theorem 1])
-- statement:
--   Let $X\subseteq\mathbb R^d$ be open and convex, let $\rho$ be a measure on $\mathbb R^d$ (the density $e^{-\varphi}$, possibly on a subspace) whose log-Laplace transform $\psi=\varphi^\sharp$ is finite on $X$, and assume $\psi$ is strictly convex and twice differentiable on $X$. Let $\pi$ be a probability measure on $X$ satisfying an $\alpha$-$\psi$-PI ($\alpha>0$), let $\tau\in\mathbb N$, and run Algorithm 1 (forwards step $y_k\sim T_{x_k}\rho^{*\tau}$, backwards step $x_{k+1}\sim T_{y_k}(e^{-\tau\psi}\pi)$) from $x_0\sim\mu_0$ with $\mu_0\ll\pi$. Then for every $k\in\mathbb N$ the law $\mu_k$ of $x_k$ satisfies $\mu_k\ll\pi$ and
--
--   $$\chi^2(\mu_k\|\pi)\le\frac{1}{(1+\alpha/\tau)^{2k}}\,\chi^2(\mu_0\|\pi).$$
--
--   This is the convergence theorem of functional stochastic localization: a $\psi$-Poincaré inequality gives geometric $\chi^2$ decay of the ideal proximal sampler, at rate governed by $\alpha/\tau$. The paper uses it with $\psi$ the log barrier and $\pi=\pi_t$.
--
--   Differences from the source:
--   - encoding: φ with ψ = φ♯ (Definition 1), exp(−φ) a density with respect to Lebesgue measure on ℝᵈ or on a linear subspace L → a measure ρ on ℝᵈ that is the image of g·Leb_{ℝᵏ} (g ≥ 0 measurable) under a linear isometry ℝᵏ → ℝᵈ, with ∫ e^{⟨x,y⟩}ρ(dy) = e^{ψ(x)} on X; reason: Lebesgue measure on L is the image of Lebesgue measure on ℝᵏ under an isometry onto L, so these are exactly Definition 1's densities
--   - encoding: Definition 2's setting: X open, ψ : X → ℝ strictly convex and twice differentiable → X open and convex, ψ strictly convex on X, ψ and ∇ψ differentiable on X; reason: strict convexity on X presupposes a convex domain
--   - encoding: xₖ has a density µₖ → the clause µₖ ≪ π; χ² in [0, ∞]; reason: the density is with respect to π (it is π-a.e. defined)
--   - encoding: α-ψ-PI, τ ∈ N, k ∈ N → α > 0, τ ≥ 1, every k : ℕ (k = 0 included, where the bound is an equality); reason: the constant of a Poincaré inequality is positive; the paper's N starts at 1; k = 0 is trivially true
--   - encoding: Algorithm 1 run from x₀ ∼ µ₀ → the law lltProxLaw ρ π ψ τ µ₀ k obtained by binding the forwards law T_x(ρ^{∗τ}) and the backwards law T_y(e^{−τψ}π) k times; reason: these are the conditionals of the joint density (5)
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 1, p.9 (PDF p.11), citing [GST26, Theorem 1]; Definitions 1–2 and Algorithm 1, pp.8–9

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_PsiPI
import Definitions.Def_PolySampIso_LLT

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PolySampIso

/-- **Proposition 1** (χ² contraction of the LLT proximal sampler, [GST26, Theorem 1]).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 1, p.9 (PDF p.11):

"Proposition 1 (Theorem 1, [GST26]). Assume π satisfies an α-ψ-PI and x0 ∼ µ0 with µ0 ≪ π. Then,
for every k ∈ N, xk in Algorithm 1 has a density µk that satisfies
χ2(µk∥π) ≤ 1/(1 + α/τ)^{2k} χ2(µ0∥π)."

**Formalization Note.** The setting is §2.2's, at its generality: a measure `ρ` on `ℝᵈ` (the
density `exp(−φ)` of Definition 1, possibly on a subspace) with `ψ = φ♯` on an open convex `X`.
Definition 1 makes `exp(−φ)` a density with respect to Lebesgue measure on `ℝᵈ` or on a linear
subspace `L`; this is `hρ`: `ρ` is the image of `g · Leb_{ℝᵏ}` (`g ≥ 0` measurable) under a linear
isometry `ℝᵏ → ℝᵈ` onto `L` (`k = d` and the identity is the full-dimensional case). Further,
`ψ` strictly convex and twice differentiable on `X` (Definition 2), a target `π ∈ P(X)`, and a step
size `τ ∈ N` (`τ ≥ 1`). `lltProxLaw ρ π ψ τ μ₀ k = Law(x_k)` for Algorithm 1. "Has a density" is the
clause `μ_k ≪ π`. `α > 0` is implicit in "α-ψ-PI". `χ²` is in `ℝ≥0∞`; the case `k = 0` is included. -/
theorem proposition_1 {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψc : StrictConvexOn ℝ X ψ)
    (hψd : DifferentiableOn ℝ ψ X) (hψd2 : DifferentiableOn ℝ (fderiv ℝ ψ) X)
    (hρ : ∃ (k : ℕ) (e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
      (g : EuclideanSpace ℝ (Fin k) → ℝ≥0), Measurable g ∧
        ρ = (volume.withDensity fun z => (g z : ℝ≥0∞)).map e)
    (hLLT : IsLLTOn ρ ψ X)
    (π : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure π] (hπX : π Xᶜ = 0)
    (α : ℝ) (hα : 0 < α) (hPI : SatisfiesPsiPI π X ψ α)
    (τ : ℕ) (hτ : 1 ≤ τ)
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ ≪ π)
    (k : ℕ) :
    lltProxLaw ρ π ψ τ μ₀ k ≪ π ∧
      chiSq (lltProxLaw ρ π ψ τ μ₀ k) π ≤
        ENNReal.ofReal (1 / (1 + α / τ) ^ (2 * k)) * chiSq μ₀ π := by sorry

end PolySampIso
