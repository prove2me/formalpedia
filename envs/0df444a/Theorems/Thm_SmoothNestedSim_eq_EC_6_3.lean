-- Prove2me | Theorems.Thm_SmoothNestedSim_eq_EC_6_3
-- name    : SmoothNestedSim.eq_EC_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:20.783794+00:00
-- url     : https://prove2.me/theorems/fea0f9c2-d09d-4c9d-bf41-317c6443f408
-- title:
--   (EC.6.3): the Monte Carlo term $I_1=\bigl|\mathbb E[\eta(f(X))]-\frac1n\sum_i\eta(f(\mathbf x_i))\bigr|=O_{\mathbb P}(n^{-1/2})$
-- statement:
--   Let $\nu>0$, $\ell>0$; let $\Omega$ and the law $\mu_X$ of $X$ satisfy Assumption 2, let $f\in\mathcal N_\Psi(\Omega)$ (Assumption 3) and let $\eta:\mathbb R\to\mathbb R$ be continuous. For every sequence $n_k\ge1$, with $\mathbf x_1,\dots,\mathbf x_{n_k}$ i.i.d. $\mu_X$,
--
--   $$
--   I_1=\Bigl|\mathbb E[\eta(f(X))]-\frac1{n_k}\sum_{i=1}^{n_k}\eta(f(\mathbf x_i))\Bigr| = O_{\mathbb P}\bigl(n_k^{-1/2}\bigr).
--   $$
--
--   This is the Monte Carlo part of the error decomposition (EC.6.1) of the KRR-driven estimator.
--
--   Differences from the source:
--   - generalization: η twice differentiable with bounded first and second derivatives on f(Ω) (the setting of Theorem 1) → η continuous; reason: the bound uses only that η(f(·)) is bounded on Ω, which holds for continuous η; a twice-differentiable η is continuous
--   - reading: I₁ = O_ℙ(n^{−1/2}) as n grows → for every sequence n_k ≥ 1; reason: the argument (bounded i.i.d. summands) gives the bound uniformly in n
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - reading: the support of X is a bounded convex set Ω and X has a probability density bounded above and below away from zero (Assumption 2, p.15) → μX = ρ·(Lebesgue measure restricted to Ω) with c ≤ ρ(x) ≤ C for x ∈ Ω, some c > 0; reason: "support" is read as the set carrying the law (μX(Ωᶜ) = 0) on which the density is bounded below; when Ω is closed this is the topological support, and for any bounded convex Ω the law is the same as for its closure
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, proof of Theorem 1, (EC.6.1) and (EC.6.3), p.ec13 (PDF p.59)

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_IsDesignLaw
import Definitions.Def_SmoothNestedSim_nestedExpectation

open MeasureTheory

namespace SmoothNestedSim

/-- **(EC.6.3): the Monte Carlo term `I₁ = O_ℙ(n^{−1/2})`** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, proof of Theorem 1, (EC.6.1) and (EC.6.3), p.ec13 = PDF p.59):
"`η(f(xᵢ))`'s are bounded random variables, thereby being sub-Gaussian. Then, the central
limit theorem implies that `I₁ = O_ℙ(n^{−1/2})`", where
`I₁ = |𝔼[η(f(X))] − (1/n) Σᵢ η(f(xᵢ))|`.

Under Assumption 2 (law `μX` of `X`) and Assumption 3 (`f ∈ N_Ψ(Ω)`), for every continuous
`η : ℝ → ℝ` and every sequence of sample sizes `n_k ≥ 1`, with `x₁, …, x_{n_k}` i.i.d. `μX`,
`I₁ = O_ℙ(n_k^{−1/2})`.

**Formalization Note.** `η` is only assumed continuous (the paper's `η` is twice
differentiable, hence continuous). -/
theorem eq_EC_6_3 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μX : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μX] (hX : IsDesignLaw Ω μX)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω)
    (η : ℝ → ℝ) (hη : Continuous η) (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) :
    IsBigOP (fun k => Measure.pi (fun _ : Fin (n k) => μX))
      (fun k x => |nestedExpectation μX η f - (1 / (n k : ℝ)) * ∑ i, η (f (x i))|)
      (fun k => (n k : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end SmoothNestedSim
