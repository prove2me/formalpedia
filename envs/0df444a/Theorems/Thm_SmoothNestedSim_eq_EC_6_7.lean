-- Prove2me | Theorems.Thm_SmoothNestedSim_eq_EC_6_7
-- name    : SmoothNestedSim.eq_EC_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:11.161413+00:00
-- url     : https://prove2.me/theorems/ac79a25a-6871-4c05-8dca-624b2ecc87f0
-- title:
--   (EC.6.7): $|\hat\theta_{n,m}-\theta|=O_{\mathbb P}(n^{-1/2}+\lambda^{1/2}+(mn)^{-1}\lambda^{-d/(2\nu+d)})$ when $\lambda=O(1)$
-- statement:
--   Throughout, $\nu>0$ and $\ell>0$; $\Omega\subseteq\mathbb R^d$ and the law $\mu_X$ of $X$ satisfy Assumption 2 (bounded convex support, density bounded above and below away from zero); $f\in\mathcal N_\Psi(\Omega)$, the RKHS of the Matérn kernel of smoothness $\nu$ (Assumption 3). At index $k$ there are $n_k\ge1$ outer-level scenarios $\mathbf x_1,\dots,\mathbf x_{n_k}$ i.i.d. $\mu_X$ and, given them, a noise array $(\epsilon_{ij})$ satisfying Assumption 1 with a fixed variance proxy $\sigma^2$ (independent, zero-mean $\mathrm{subG}(\sigma^2)$, identically distributed in $j$, possibly heteroscedastic); the inner samples are $y_{ij}=f(\mathbf x_i)+\epsilon_{ij}$, $j=1,\dots,m_k$, and $\hat f$ is the KRR fit (6) with the Matérn kernel of the same $\nu$ and length-scale $\ell$ and regularization $\lambda_k>0$.
--
--   Let $\eta:\mathbb R\to\mathbb R$ be twice differentiable with $\eta'$ and $\eta''$ bounded on $f(\Omega)$, $\theta=\mathbb E[\eta(f(X))]$ and $\hat\theta_{n,m}=n^{-1}\sum_i\eta(\hat f(\mathbf x_i))$. Then, for every sequence of sample sizes $n_k,m_k\ge1$ and regularization parameters $\lambda_k>0$:
--
--   1. $$|\hat\theta_{n_k,m_k}-\theta| = O_{\mathbb P}\Bigl(n_k^{-1/2}+\lambda_k^{1/2}+(m_kn_k)^{-1/2}+(m_kn_k)^{-1}\lambda_k^{-\frac{d}{2\nu+d}}+(m_kn_k)^{-\frac{2\nu+d}{2\nu+2d}}+\lambda_k\Bigr);$$
--   2. if moreover $\lambda_k=O(1)$, then $$|\hat\theta_{n_k,m_k}-\theta| = O_{\mathbb P}\Bigl(n_k^{-1/2}+\lambda_k^{1/2}+(m_kn_k)^{-1}\lambda_k^{-\frac{d}{2\nu+d}}\Bigr).$$
--
--   This is the non-asymptotic error bound that Theorem 1 optimizes over the allocation of the budget; p.17 states the second form in prose.
--
--   Differences from the source:
--   - reading: Assumption 1: the εᵢⱼ are independent, zero-mean subG(σ²), identically distributed in j (p.15) → conditionally on the design x₁,…,xₙ, the εᵢⱼ are independent with laws ξᵢ (depending on i and on the design) that are zero-mean subG(σ²): the noise array has conditional law ⊗ᵢ⊗ⱼ ξᵢ; reason: read literally, with nothing linking ε to the xᵢ, Theorem 1 is false (εᵢ₁ = g(xᵢ) + ξᵢ with E g(X) = 0, m = 1, η(z) = z²); the paper samples yᵢⱼ from the conditional law of Y given X = xᵢ (§2.1, p.8) and computes variances with the design fixed (EC.4.7)
--   - reading: the statement fixes no relation between n, m and λ → it is stated for every sequence (n_k, m_k ≥ 1, λ_k > 0); reason: the paper gives no regime and its proof is non-asymptotic
--   - reading: η twice differentiable with bounded first- and second-order derivatives (Theorem 1, p.17) → η differentiable on ℝ with deriv η differentiable on ℝ, and |η′|, |η″| bounded on f(Ω); reason: §4.2 (i), p.16 pins the bounds down as sup over {f(x) : x ∈ Ω}, and the proof (EC.6.5)–(EC.6.6) uses exactly those constants
--   - encoding: η : ℝ^d ↦ ℝ (§2 (i), p.8) → η : ℝ → ℝ; reason: η is applied to the real number f(x) and η′, η″ are scalar derivatives; ℝ^d is a typo
--   - encoding: λ = O(1) → ∃ C > 0, λ_k ≤ C·1 for all k large enough; reason: p.8's definition of O(·)
--   - encoding: asymptotics in the sample sizes n, m (and λ), all on one probability space → an index k with sample sizes n_k, m_k ≥ 1, λ_k > 0 and the data at index k on its own canonical space ((ℝ^d)^{n_k} × ℝ^{n_k×m_k}, μX^{⊗n_k} ⊗ κ_k); reason: O_ℙ only involves the law of the data at each index, which is the same on any probability space
--   - encoding: zero-mean subG(σ²): 𝔼[e^{t(Z−𝔼Z)}] ≤ e^{σ²t²/2} and 𝔼Z = 0 (Definition 1, p.15) → HasSubgaussianMGF id σ² (𝔼[e^{tZ}] ≤ e^{σ²t²/2}, exponential moments integrable); reason: for a zero-mean Z the two inequalities coincide, and the Mathlib predicate forces 𝔼Z = 0 (proved in the verification file)
--   - encoding: the conditional law of the noise given the design → a Markov kernel κ from designs to noise arrays whose value at every design has the product form; reason: a conditional law can be modified on a null set of designs; only its values almost everywhere affect the data law
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - encoding: f̂ := argmin of (5), equal to r(x)ᵀ(R + nλI)⁻¹ȳ (6) → f̂ is defined by the closed form r(x)ᵀ(R + nλI)⁻¹ȳ; reason: the identity is the separate milestone eq_6_krr_closed_form
--   - reading: the support of X is a bounded convex set Ω and X has a probability density bounded above and below away from zero (Assumption 2, p.15) → μX = ρ·(Lebesgue measure restricted to Ω) with c ≤ ρ(x) ≤ C for x ∈ Ω, some c > 0; reason: "support" is read as the set carrying the law (μX(Ωᶜ) = 0) on which the density is bounded below; when Ω is closed this is the topological support, and for any bounded convex Ω the law is the same as for its closure
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, proof of Theorem 1, (EC.6.7), p.ec14 (PDF p.60); also p.17

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_IsDesignLaw
import Definitions.Def_SmoothNestedSim_IsNoiseKernel
import Definitions.Def_SmoothNestedSim_dataLaw
import Definitions.Def_SmoothNestedSim_krrFit
import Definitions.Def_SmoothNestedSim_thetaHat
import Definitions.Def_SmoothNestedSim_nestedExpectation

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace SmoothNestedSim

/-- **(EC.6.7): the combined error bound** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, proof of Theorem 1, (EC.6.7), p.ec14 = PDF p.60; also stated on p.17):
"`|θ̂_{n,m} − θ| = O_ℙ(n^{−1/2} + λ^{1/2} + (mn)^{−1/2} + (mn)^{−1}λ^{−d/(2ν+d)} + (mn)^{−(2ν+d)/(2ν+2d)} + λ)
= O_ℙ(n^{−1/2} + λ^{1/2} + (mn)^{−1}λ^{−d/(2ν+d)})`, where the second inequality holds because
`λ = O(1)`, `(mn)^{−1/2} ≤ n^{−1/2}`, and `(mn)^{−(2ν+d)/(2ν+2d)} ≤ n^{−1/2}`."

Let `𝒯(·) = 𝔼[η(·)]` with `η` twice differentiable and `η′`, `η″` bounded on `f(Ω)`, so that
`θ = 𝔼[η(f(X))]` and `θ̂_{n,m} = n⁻¹ Σᵢ η(f̂(xᵢ))`. The data at index `k` are `n_k` outer-level scenarios `x₁, …, x_{n_k}` i.i.d. with law `μX`
(Assumption 2: support a bounded convex `Ω`, density bounded above and below away from zero)
and, given them, a noise array `(ϵᵢⱼ)` with conditional law `κ_k` satisfying Assumption 1
(independent zero-mean `subG(σ²)`, identically distributed in `j`); `yᵢⱼ = f(xᵢ) + ϵᵢⱼ` with
`f ∈ N_Ψ(Ω)` (Assumption 3), and `f̂` is the KRR fit (6) with the Matérn kernel of the same
smoothness `ν` and length-scale `ℓ > 0` and regularization `λ_k > 0`.
For every sequence of sample sizes `n_k, m_k ≥ 1` and regularization parameters `λ_k > 0`:
(a) the six-term bound holds; (b) if moreover `λ_k = O(1)`, the three-term bound holds.

**Formalization Note.** "Twice differentiable" is `Differentiable ℝ η` and
`Differentiable ℝ (deriv η)` on all of `ℝ`; the derivative bounds are on the range `f(Ω)`, as
in §4.2 (i), p.16. `λ = O(1)` is p.8's `O(·)`: `λ_k ≤ C` for some `C > 0` and all `k` large
enough. -/
theorem eq_EC_6_7 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μX : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μX] (hX : IsDesignLaw Ω μX)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω)
    (σsq : ℝ≥0) (n m : ℕ → ℕ) (hn : ∀ k, 0 < n k) (hm : ∀ k, 0 < m k)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k)
    (κ : ∀ k, Kernel (Fin (n k) → EuclideanSpace ℝ (Fin d)) (Fin (n k) → Fin (m k) → ℝ))
    (hκ : ∀ k, IsNoiseKernel σsq (κ k))
    (η : ℝ → ℝ) (hη : Differentiable ℝ η) (hη2 : Differentiable ℝ (deriv η))
    (hηb : ∃ B : ℝ, ∀ x ∈ Ω, |deriv η (f x)| ≤ B ∧ |deriv (deriv η) (f x)| ≤ B) :
    IsBigOP (fun k => dataLaw μX (κ k))
        (fun k ω => |thetaHat ν ℓ (lam k) η f ω - nestedExpectation μX η f|)
        (fun k => (n k : ℝ) ^ (-(1 / 2 : ℝ)) + Real.sqrt (lam k) +
          ((m k : ℝ) * n k) ^ (-(1 / 2 : ℝ)) +
          ((m k : ℝ) * n k)⁻¹ * lam k ^ (-((d : ℝ) / (2 * ν + d))) +
          ((m k : ℝ) * n k) ^ (-((2 * ν + d) / (2 * ν + 2 * d))) + lam k) ∧
      ((∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, lam k ≤ C * 1) →
        IsBigOP (fun k => dataLaw μX (κ k))
          (fun k ω => |thetaHat ν ℓ (lam k) η f ω - nestedExpectation μX η f|)
          (fun k => (n k : ℝ) ^ (-(1 / 2 : ℝ)) + Real.sqrt (lam k) +
            ((m k : ℝ) * n k)⁻¹ * lam k ^ (-((d : ℝ) / (2 * ν + d))))) := by sorry

end SmoothNestedSim
