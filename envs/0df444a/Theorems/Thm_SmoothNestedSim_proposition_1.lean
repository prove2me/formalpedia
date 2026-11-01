-- Prove2me | Theorems.Thm_SmoothNestedSim_proposition_1
-- name    : SmoothNestedSim.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:02.536168+00:00
-- url     : https://prove2.me/theorems/2462f422-c444-4fd3-97c1-e09de409f9aa
-- title:
--   Proposition 1: $\bigl|\frac1n\sum_i\varphi(f(\mathbf x_i))(f(\mathbf x_i)-\hat f(\mathbf x_i))\bigr|=O_{\mathbb P}(\lambda^{1/2}+(mn)^{-1/2})$
-- statement:
--   Throughout, $\nu>0$ and $\ell>0$; $\Omega\subseteq\mathbb R^d$ and the law $\mu_X$ of $X$ satisfy Assumption 2 (bounded convex support, density bounded above and below away from zero); $f\in\mathcal N_\Psi(\Omega)$, the RKHS of the Matérn kernel of smoothness $\nu$ (Assumption 3). At index $k$ there are $n_k\ge1$ outer-level scenarios $\mathbf x_1,\dots,\mathbf x_{n_k}$ i.i.d. $\mu_X$ and, given them, a noise array $(\epsilon_{ij})$ satisfying Assumption 1 with a fixed variance proxy $\sigma^2$ (independent, zero-mean $\mathrm{subG}(\sigma^2)$, identically distributed in $j$, possibly heteroscedastic); the inner samples are $y_{ij}=f(\mathbf x_i)+\epsilon_{ij}$, $j=1,\dots,m_k$, and $\hat f$ is the KRR fit (6) with the Matérn kernel of the same $\nu$ and length-scale $\ell$ and regularization $\lambda_k>0$.
--
--   Let $\varphi$ be bounded on $\{f(\mathbf x):\mathbf x\in\Omega\}$. Then, for every sequence of sample sizes $n_k,m_k\ge1$ and regularization parameters $\lambda_k>0$,
--
--   $$
--   \Bigl|\frac1{n_k}\sum_{i=1}^{n_k}\varphi(f(\mathbf x_i))\bigl(f(\mathbf x_i)-\hat f(\mathbf x_i)\bigr)\Bigr| = O_{\mathbb P}\bigl(\lambda_k^{1/2}+(m_kn_k)^{-1/2}\bigr).
--   $$
--
--   With $\varphi=\eta'$ this bounds the linear term $I_{21}$ of the Taylor expansion of the plug-in error, which is the step where the KRR estimator achieves a square-root rate that a pointwise error bound would not give (Remark 3).
--
--   **Formalization Note** $\varphi$ is a function on $\mathbb R$ bounded on $f(\Omega)$; only those values enter.
--
--   Differences from the source:
--   - reading: Assumption 1: the εᵢⱼ are independent, zero-mean subG(σ²), identically distributed in j (p.15) → conditionally on the design x₁,…,xₙ, the εᵢⱼ are independent with laws ξᵢ (depending on i and on the design) that are zero-mean subG(σ²): the noise array has conditional law ⊗ᵢ⊗ⱼ ξᵢ; reason: read literally, with nothing linking ε to the xᵢ, Theorem 1 is false (εᵢ₁ = g(xᵢ) + ξᵢ with E g(X) = 0, m = 1, η(z) = z²); the paper samples yᵢⱼ from the conditional law of Y given X = xᵢ (§2.1, p.8) and computes variances with the design fixed (EC.4.7)
--   - reading: the statement fixes no relation between n, m and λ → it is stated for every sequence (n_k, m_k ≥ 1, λ_k > 0); reason: the paper gives no regime and its proof is non-asymptotic
--   - encoding: asymptotics in the sample sizes n, m (and λ), all on one probability space → an index k with sample sizes n_k, m_k ≥ 1, λ_k > 0 and the data at index k on its own canonical space ((ℝ^d)^{n_k} × ℝ^{n_k×m_k}, μX^{⊗n_k} ⊗ κ_k); reason: O_ℙ only involves the law of the data at each index, which is the same on any probability space
--   - encoding: φ : {f(x) : x ∈ Ω} ↦ ℝ bounded → φ : ℝ → ℝ with |φ(f(x))| ≤ C for x ∈ Ω; reason: only the values on f(Ω) enter, since the xᵢ lie in Ω almost surely
--   - encoding: zero-mean subG(σ²): 𝔼[e^{t(Z−𝔼Z)}] ≤ e^{σ²t²/2} and 𝔼Z = 0 (Definition 1, p.15) → HasSubgaussianMGF id σ² (𝔼[e^{tZ}] ≤ e^{σ²t²/2}, exponential moments integrable); reason: for a zero-mean Z the two inequalities coincide, and the Mathlib predicate forces 𝔼Z = 0 (proved in the verification file)
--   - encoding: the conditional law of the noise given the design → a Markov kernel κ from designs to noise arrays whose value at every design has the product form; reason: a conditional law can be modified on a null set of designs; only its values almost everywhere affect the data law
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - encoding: f̂ := argmin of (5), equal to r(x)ᵀ(R + nλI)⁻¹ȳ (6) → f̂ is defined by the closed form r(x)ᵀ(R + nλI)⁻¹ȳ; reason: the identity is the separate milestone eq_6_krr_closed_form
--   - reading: the support of X is a bounded convex set Ω and X has a probability density bounded above and below away from zero (Assumption 2, p.15) → μX = ρ·(Lebesgue measure restricted to Ω) with c ≤ ρ(x) ≤ C for x ∈ Ω, some c > 0; reason: "support" is read as the set carrying the law (μX(Ωᶜ) = 0) on which the density is bounded below; when Ω is closed this is the topological support, and for any bounded convex Ω the law is the same as for its closure
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, Proposition 1, p.17

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_IsDesignLaw
import Definitions.Def_SmoothNestedSim_IsNoiseKernel
import Definitions.Def_SmoothNestedSim_dataLaw
import Definitions.Def_SmoothNestedSim_krrFit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SmoothNestedSim

/-- **Proposition 1** (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6,
Proposition 1, p.17): "Suppose `φ : {f(x) : x ∈ Ω} ↦ ℝ` is bounded, and Assumptions 1–3
hold. Then, `|(1/n) Σᵢ φ(f(xᵢ))(f(xᵢ) − f̂(xᵢ))| = O_ℙ(λ^{1/2} + (mn)^{−1/2})`."

The data at index `k` are `n_k` outer-level scenarios `x₁, …, x_{n_k}` i.i.d. with law `μX`
(Assumption 2: support a bounded convex `Ω`, density bounded above and below away from zero)
and, given them, a noise array `(ϵᵢⱼ)` with conditional law `κ_k` satisfying Assumption 1
(independent zero-mean `subG(σ²)`, identically distributed in `j`); `yᵢⱼ = f(xᵢ) + ϵᵢⱼ` with
`f ∈ N_Ψ(Ω)` (Assumption 3), and `f̂` is the KRR fit (6) with the Matérn kernel of the same
smoothness `ν` and length-scale `ℓ > 0` and regularization `λ_k > 0`.
For every sequence of sample sizes `n_k, m_k ≥ 1` and regularization parameters `λ_k > 0`,
and every `φ` bounded on `f(Ω)`,
`|(1/n_k) Σᵢ φ(f(xᵢ))(f(xᵢ) − f̂(xᵢ))| = O_ℙ(λ_k^{1/2} + (m_k n_k)^{−1/2})`.

**Formalization Note.** `φ` is a function on `ℝ` that is bounded on `f(Ω)`; only its values
on `f(Ω)` enter, since the `xᵢ` lie in `Ω` almost surely. The proposition carries no relation
between `n`, `m` and `λ`, so none is assumed. -/
theorem proposition_1 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μX : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μX] (hX : IsDesignLaw Ω μX)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω)
    (σsq : ℝ≥0) (n m : ℕ → ℕ) (hn : ∀ k, 0 < n k) (hm : ∀ k, 0 < m k)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k)
    (κ : ∀ k, Kernel (Fin (n k) → EuclideanSpace ℝ (Fin d)) (Fin (n k) → Fin (m k) → ℝ))
    (hκ : ∀ k, IsNoiseKernel σsq (κ k))
    (φ : ℝ → ℝ) (hφ : ∃ C : ℝ, ∀ x ∈ Ω, |φ (f x)| ≤ C) :
    IsBigOP (fun k => dataLaw μX (κ k))
      (fun k ω => |(1 / (n k : ℝ)) *
        ∑ i, φ (f (ω.1 i)) * (f (ω.1 i) - krrFit ν ℓ (lam k) f ω (ω.1 i))|)
      (fun k => Real.sqrt (lam k) + ((m k : ℝ) * n k) ^ (-(1 / 2 : ℝ))) := by sorry

end SmoothNestedSim
