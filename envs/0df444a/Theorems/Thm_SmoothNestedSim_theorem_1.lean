-- Prove2me | Theorems.Thm_SmoothNestedSim_theorem_1
-- name    : SmoothNestedSim.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:37.619282+00:00
-- url     : https://prove2.me/theorems/584c19b4-6aa4-40d4-be58-ec31a4f4c21e
-- title:
--   Theorem 1: $|\hat\theta_{n,m}-\theta|=O_{\mathbb P}(\Gamma^{-1/2})$ if $\nu\ge d/2$ and $O_{\mathbb P}(\Gamma^{-(2\nu+d)/(2\nu+3d)})$ if $\nu<d/2$
-- statement:
--   Throughout, $\nu>0$ and $\ell>0$; $\Omega\subseteq\mathbb R^d$ and the law $\mu_X$ of $X$ satisfy Assumption 2 (bounded convex support, density bounded above and below away from zero); $f\in\mathcal N_\Psi(\Omega)$, the RKHS of the Matérn kernel of smoothness $\nu$ (Assumption 3). At index $k$ there are $n_k\ge1$ outer-level scenarios $\mathbf x_1,\dots,\mathbf x_{n_k}$ i.i.d. $\mu_X$ and, given them, a noise array $(\epsilon_{ij})$ satisfying Assumption 1 with a fixed variance proxy $\sigma^2$ (independent, zero-mean $\mathrm{subG}(\sigma^2)$, identically distributed in $j$, possibly heteroscedastic); the inner samples are $y_{ij}=f(\mathbf x_i)+\epsilon_{ij}$, $j=1,\dots,m_k$, and $\hat f$ is the KRR fit (6) with the Matérn kernel of the same $\nu$ and length-scale $\ell$ and regularization $\lambda_k>0$.
--
--   Let $\eta:\mathbb R\to\mathbb R$ be twice differentiable with $\eta'$ and $\eta''$ bounded on $f(\Omega)$, $\theta=\mathbb E[\eta(f(X))]$ and $\hat\theta_{n,m}=n^{-1}\sum_{i=1}^n\eta(\hat f(\mathbf x_i))$. Let the simulation budget $\Gamma_k=n_km_k$ tend to infinity. Then for every such allocation:
--
--   1. if $\nu\ge d/2$, $n_k\asymp\Gamma_k$, $m_k\asymp1$ and $\lambda_k\asymp\Gamma_k^{-1}$, then
--   $$|\hat\theta_{n_k,m_k}-\theta| = O_{\mathbb P}\bigl(\Gamma_k^{-1/2}\bigr);$$
--   2. if $0<\nu<d/2$, $n_k\asymp\Gamma_k^{\frac{2(2\nu+d)}{2\nu+3d}}$, $m_k\asymp\Gamma_k^{\frac{d-2\nu}{2\nu+3d}}$ and $\lambda_k\asymp\Gamma_k^{-\frac{2(2\nu+d)}{2\nu+3d}}$, then
--   $$|\hat\theta_{n_k,m_k}-\theta| = O_{\mathbb P}\Bigl(\Gamma_k^{-\frac{2\nu+d}{2\nu+3d}}\Bigr).$$
--
--   The exponent $\kappa=\frac{2\nu+d}{2\nu+3d}$ increases from $1/3$ (the cubic-root rate of standard nested simulation) as $\nu\to0$ to $1/2$ at $\nu=d/2$, so the smoothness of $f$ bridges the cubic-root and the square-root (Monte Carlo) rate in every dimension $d$.
--
--   **Formalization Note** $O_{\mathbb P}$ and $\asymp$ are those of p.8.
--
--   Differences from the source:
--   - reading: Assumption 1: the εᵢⱼ are independent, zero-mean subG(σ²), identically distributed in j (p.15) → conditionally on the design x₁,…,xₙ, the εᵢⱼ are independent with laws ξᵢ (depending on i and on the design) that are zero-mean subG(σ²): the noise array has conditional law ⊗ᵢ⊗ⱼ ξᵢ; reason: read literally, with nothing linking ε to the xᵢ, Theorem 1 is false (εᵢ₁ = g(xᵢ) + ξᵢ with E g(X) = 0, m = 1, η(z) = z²); the paper samples yᵢⱼ from the conditional law of Y given X = xᵢ (§2.1, p.8) and computes variances with the design fixed (EC.4.7)
--   - reading: η twice differentiable with bounded first- and second-order derivatives (Theorem 1, p.17) → η differentiable on ℝ with deriv η differentiable on ℝ, and |η′|, |η″| bounded on f(Ω); reason: §4.2 (i), p.16 pins the bounds down as sup over {f(x) : x ∈ Ω}, and the proof (EC.6.5)–(EC.6.6) uses exactly those constants
--   - encoding: η : ℝ^d ↦ ℝ (§2 (i), p.8) → η : ℝ → ℝ; reason: η is applied to the real number f(x) and η′, η″ are scalar derivatives; ℝ^d is a typo
--   - reading: "κ = … by setting n ≍ …, m ≍ …, λ ≍ …" → the rate holds for every allocation (n_k, m_k, λ_k) satisfying the ≍ relations; reason: the proof (p.ec14) uses only the relations; the existential reading would be weaker
--   - encoding: the budget Γ = nm grows (asymptotics in Γ) → an index k with Γ_k = n_k m_k → ∞; reason: Γ is an integer that cannot always be factored as prescribed, so the allocation is indexed by k
--   - encoding: asymptotics in the sample sizes n, m (and λ), all on one probability space → an index k with sample sizes n_k, m_k ≥ 1, λ_k > 0 and the data at index k on its own canonical space ((ℝ^d)^{n_k} × ℝ^{n_k×m_k}, μX^{⊗n_k} ⊗ κ_k); reason: O_ℙ only involves the law of the data at each index, which is the same on any probability space
--   - encoding: zero-mean subG(σ²): 𝔼[e^{t(Z−𝔼Z)}] ≤ e^{σ²t²/2} and 𝔼Z = 0 (Definition 1, p.15) → HasSubgaussianMGF id σ² (𝔼[e^{tZ}] ≤ e^{σ²t²/2}, exponential moments integrable); reason: for a zero-mean Z the two inequalities coincide, and the Mathlib predicate forces 𝔼Z = 0 (proved in the verification file)
--   - encoding: the conditional law of the noise given the design → a Markov kernel κ from designs to noise arrays whose value at every design has the product form; reason: a conditional law can be modified on a null set of designs; only its values almost everywhere affect the data law
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - encoding: f̂ := argmin of (5), equal to r(x)ᵀ(R + nλI)⁻¹ȳ (6) → f̂ is defined by the closed form r(x)ᵀ(R + nλI)⁻¹ȳ; reason: the identity is the separate milestone eq_6_krr_closed_form
--   - reading: the support of X is a bounded convex set Ω and X has a probability density bounded above and below away from zero (Assumption 2, p.15) → μX = ρ·(Lebesgue measure restricted to Ω) with c ≤ ρ(x) ≤ C for x ∈ Ω, some c > 0; reason: "support" is read as the set carrying the law (μX(Ωᶜ) = 0) on which the density is bounded below; when Ω is closed this is the topological support, and for any bounded convex Ω the law is the same as for its closure
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, Theorem 1, p.17

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_IsDesignLaw
import Definitions.Def_SmoothNestedSim_IsNoiseKernel
import Definitions.Def_SmoothNestedSim_dataLaw
import Definitions.Def_SmoothNestedSim_krrFit
import Definitions.Def_SmoothNestedSim_IsAsympEquiv
import Definitions.Def_SmoothNestedSim_thetaHat
import Definitions.Def_SmoothNestedSim_nestedExpectation

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace SmoothNestedSim

/-- **Theorem 1** (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6,
Theorem 1, p.17): "Let `𝒯(·) = 𝔼[η(·)]` and `η` be a twice-differentiable function with
bounded first- and second-order derivatives. Suppose Assumptions 1–3 hold. Then,
`|θ̂_{n,m} − θ| = O_ℙ(Γ^{−κ})`, where `κ` is specified as follows:
(i) If `ν ≥ d/2`, then `κ = 1/2` by setting `n ≍ Γ`, `m ≍ 1`, and `λ ≍ Γ^{−1}`.
(ii) If `0 < ν < d/2`, then `κ = (2ν+d)/(2ν+3d)` by setting `n ≍ Γ^{2(2ν+d)/(2ν+3d)}`,
`m ≍ Γ^{(d−2ν)/(2ν+3d)}`, and `λ ≍ Γ^{−2(2ν+d)/(2ν+3d)}`."

The data at index `k` are `n_k` outer-level scenarios `x₁, …, x_{n_k}` i.i.d. with law `μX`
(Assumption 2: support a bounded convex `Ω`, density bounded above and below away from zero)
and, given them, a noise array `(ϵᵢⱼ)` with conditional law `κ_k` satisfying Assumption 1
(independent zero-mean `subG(σ²)`, identically distributed in `j`); `yᵢⱼ = f(xᵢ) + ϵᵢⱼ` with
`f ∈ N_Ψ(Ω)` (Assumption 3), and `f̂` is the KRR fit (6) with the Matérn kernel of the same
smoothness `ν` and length-scale `ℓ > 0` and regularization `λ_k > 0`.
The budget is `Γ_k = n_k m_k` (p.9) and tends to infinity. Then for **every** such allocation:
(i) if `ν ≥ d/2`, `n_k ≍ Γ_k`, `m_k ≍ 1` and `λ_k ≍ Γ_k^{−1}`, then
`|θ̂ − θ| = O_ℙ(Γ_k^{−1/2})`; (ii) if `ν < d/2`, `n_k ≍ Γ_k^{2(2ν+d)/(2ν+3d)}`,
`m_k ≍ Γ_k^{(d−2ν)/(2ν+3d)}` and `λ_k ≍ Γ_k^{−2(2ν+d)/(2ν+3d)}`, then
`|θ̂ − θ| = O_ℙ(Γ_k^{−(2ν+d)/(2ν+3d)})`.

**Formalization Note.** "By setting" is read universally over allocations satisfying the
printed `≍` relations; the asymptotic index is `k` with `Γ_k = n_k m_k → ∞`. "Twice
differentiable" is on all of `ℝ`; the derivative bounds are on the range `f(Ω)`, as pinned down
in §4.2 (i), p.16. `O_ℙ` and `≍` are p.8's. -/
theorem theorem_1 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μX : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μX] (hX : IsDesignLaw Ω μX)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω)
    (σsq : ℝ≥0) (n m : ℕ → ℕ) (hn : ∀ k, 0 < n k) (hm : ∀ k, 0 < m k)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k)
    (κ : ∀ k, Kernel (Fin (n k) → EuclideanSpace ℝ (Fin d)) (Fin (n k) → Fin (m k) → ℝ))
    (hκ : ∀ k, IsNoiseKernel σsq (κ k))
    (η : ℝ → ℝ) (hη : Differentiable ℝ η) (hη2 : Differentiable ℝ (deriv η))
    (hηb : ∃ B : ℝ, ∀ x ∈ Ω, |deriv η (f x)| ≤ B ∧ |deriv (deriv η) (f x)| ≤ B)
    (hΓ : Tendsto (fun k => n k * m k) atTop atTop) :
    (d / 2 ≤ ν →
      IsAsympEquiv (fun k => (n k : ℝ)) (fun k => (n k : ℝ) * m k) →
      IsAsympEquiv (fun k => (m k : ℝ)) (fun _ => 1) →
      IsAsympEquiv lam (fun k => ((n k : ℝ) * m k)⁻¹) →
      IsBigOP (fun k => dataLaw μX (κ k))
        (fun k ω => |thetaHat ν ℓ (lam k) η f ω - nestedExpectation μX η f|)
        (fun k => ((n k : ℝ) * m k) ^ (-(1 / 2 : ℝ)))) ∧
    (ν < d / 2 →
      IsAsympEquiv (fun k => (n k : ℝ))
        (fun k => ((n k : ℝ) * m k) ^ (2 * (2 * ν + d) / (2 * ν + 3 * d))) →
      IsAsympEquiv (fun k => (m k : ℝ))
        (fun k => ((n k : ℝ) * m k) ^ ((d - 2 * ν) / (2 * ν + 3 * d))) →
      IsAsympEquiv lam
        (fun k => ((n k : ℝ) * m k) ^ (-(2 * (2 * ν + d) / (2 * ν + 3 * d)))) →
      IsBigOP (fun k => dataLaw μX (κ k))
        (fun k ω => |thetaHat ν ℓ (lam k) η f ω - nestedExpectation μX η f|)
        (fun k => ((n k : ℝ) * m k) ^ (-((2 * ν + d) / (2 * ν + 3 * d))))) := by sorry

end SmoothNestedSim
