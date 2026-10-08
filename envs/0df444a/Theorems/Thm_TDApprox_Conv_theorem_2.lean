-- Prove2me | Theorems.Thm_TDApprox_Conv_theorem_2
-- name    : TDApprox.Conv.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:08.450982+00:00
-- url     : https://prove2.me/theorems/d7938cca-8f7f-4914-8b4b-7f531ee5a2a6
-- title:
--   Theorem 2, p. 18 — stochastic approximation with Markov noise: r_{t+1} = r_t + γ_t(A(X_t)r_t + b(X_t)) converges w.p. 1 to the root of Ar + b = 0
-- statement:
--   Let $X_t$ be a Markov process on a measurable state space $\mathcal X$ with transition kernel $\kappa$. Let $A(\cdot)$ be a $K\times K$-matrix valued and $b(\cdot)$ an $\mathbb R^K$-valued function on $\mathcal X$, and let $f$ map $\mathcal X$ into $\mathbb R^L$. Consider the iteration
--   $$r_{t+1} = r_t + \gamma_t\big(A(X_t)r_t + b(X_t)\big),$$
--   and assume:
--   1. (a) the predetermined step sizes $\gamma_t$ are nonnegative and nonincreasing, with $\sum_t\gamma_t = \infty$ and $\sum_t\gamma_t^2 < \infty$;
--   2. (b) $X_t$ has a unique invariant distribution, with expectation $E_0$, and $f$ is a bijection from the states onto a subset of $\mathbb R^L$;
--   3. (c) $A = E_0[A(X_t)]$ and $b = E_0[b(X_t)]$ are well defined and finite;
--   4. (d) $A$ is negative definite: $r'Ar < 0$ for all $r \ne 0$;
--   5. (e) for every $q > 1$ there is $\mu_q$ with $E[\|f(X_t)\|^q \mid X_0 = X] \le \mu_q(1+\|f(X)\|^q)$ for all $X$ and $t$;
--   6. (f) there are $C_1, q_1 > 0$ with $\|A(X)\| \le C_1(1+\|f(X)\|^{q_1})$ and $\|b(X)\| \le C_1(1+\|f(X)\|^{q_1})$ for all $X$;
--   7. (g) there are $C_2, q_2 > 0$ such that, for all $X$,
--   $$\sum_{t=0}^\infty \big\|E[A(X_t)\mid X_0 = X] - A\big\| \le C_2(1+\|f(X)\|^{q_2}), \qquad \sum_{t=0}^\infty \big\|E[b(X_t)\mid X_0 = X] - b\big\| \le C_2(1+\|f(X)\|^{q_2}).$$
--
--   Then there is a unique vector $r^*$ with $Ar^* + b = 0$, and $r_t$ converges to $r^*$ with probability 1.
--
--   The paper states this result without proof, as a special case of Benveniste, Métivier and Priouret (1987), Theorem 17, p. 239; it is the stochastic approximation tool from which Theorem 1(b) follows.
--
--   **Formalization Note.** The process is the Markov chain with kernel $\kappa$ started at a deterministic state $X$; convergence is claimed almost surely under its path law, for every initial state and every $r_0$. Conditional expectations given $X_0 = X$ are integrals against that path law. A bijection onto a subset of $\mathbb R^L$ is an injective map. $A(\cdot)$, $b(\cdot)$ and $f$ are assumed measurable (implicit on the page). Vector norms are Euclidean and matrix norms Frobenius; every norm bound sits under an existential constant, so this matches the page's Euclidean induced norm. The sums in (g) are required to converge, and every expectation in (e) and (g) to be finite.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 2, p. 18; stated there without proof, quoted from Benveniste, Métivier & Priouret (1987), Adaptive Algorithms and Stochastic Approximations, Theorem 17, p. 239

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Theorem 2** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 18; stated there without proof as
a special case of Benveniste, Métivier & Priouret (1987), Theorem 17, p. 239).
Let `X_t` be a Markov process on a measurable space `𝒳` with transition kernel `κ`, and consider
`r_{t+1} = r_t + γ_t (A(X_t) r_t + b(X_t))`, where
(a) `γ` is nonnegative, nonincreasing, `Σ γ_t = ∞`, `Σ γ_t² < ∞`;
(b) `X_t` has a unique invariant distribution `ν`, and `f : 𝒳 → ℝ^L` is injective (a bijection
onto a subset of `ℝ^L`);
(c) `A = E_0[A(X_t)]` and `b = E_0[b(X_t)]` are well defined and finite;
(d) `A` is negative definite;
(e) for any `q > 1` there is `μ_q` with `E[‖f(X_t)‖^q | X_0 = X] ≤ μ_q(1 + ‖f(X)‖^q)` for all `X, t`;
(f) there are `C₁, q₁ > 0` with `‖A(X)‖, ‖b(X)‖ ≤ C₁(1 + ‖f(X)‖^{q₁})` for all `X`;
(g) there are `C₂, q₂ > 0` with `Σ_t ‖E[A(X_t) | X_0 = X] − A‖ ≤ C₂(1 + ‖f(X)‖^{q₂})` and
`Σ_t ‖E[b(X_t) | X_0 = X] − b‖ ≤ C₂(1 + ‖f(X)‖^{q₂})` for all `X`.
Then `r_t` converges with probability 1 (from every initial state and every `r_0`) to `r*`, the
unique vector with `A r* + b = 0`. -/
theorem theorem_2 {𝒳 : Type*} [MeasurableSpace 𝒳] (κ : Kernel 𝒳 𝒳) [IsMarkovKernel κ]
    {K L : ℕ} (γ : ℕ → ℝ) (A : 𝒳 → Matrix (Fin K) (Fin K) ℝ) (b : 𝒳 → Fin K → ℝ)
    (f : 𝒳 → Fin L → ℝ)
    (hA_meas : ∀ k l, Measurable (fun x => A x k l)) (hb_meas : ∀ k, Measurable (fun x => b x k))
    (hf_meas : Measurable f)
    (ha : Assumption4 γ)
    (ν : Measure 𝒳) [IsProbabilityMeasure ν] (hν : κ.Invariant ν)
    (hν_unique : ∀ ν' : Measure 𝒳, IsProbabilityMeasure ν' → κ.Invariant ν' → ν' = ν)
    (hf_inj : Function.Injective f)
    (hA_int : ∀ k l, Integrable (fun x => A x k l) ν) (hb_int : ∀ k, Integrable (fun x => b x k) ν)
    (hd : ∀ r : Fin K → ℝ, r ≠ 0 →
      r ⬝ᵥ ((fun k l => ∫ x, A x k l ∂ν) *ᵥ r) < 0)
    (he : ∀ q : ℝ, 1 < q → ∃ μq : ℝ, ∀ (x : 𝒳) (t : ℕ),
      Integrable (fun ω => euclNorm (f (ω t)) ^ q) (pathLaw κ x) ∧
        ∫ ω, euclNorm (f (ω t)) ^ q ∂(pathLaw κ x) ≤ μq * (1 + euclNorm (f x) ^ q))
    (hf : ∃ C₁ q₁ : ℝ, 0 < C₁ ∧ 0 < q₁ ∧ ∀ x,
      frobNorm (A x) ≤ C₁ * (1 + euclNorm (f x) ^ q₁) ∧
        euclNorm (b x) ≤ C₁ * (1 + euclNorm (f x) ^ q₁))
    (hg : ∃ C₂ q₂ : ℝ, 0 < C₂ ∧ 0 < q₂ ∧ ∀ x : 𝒳,
      (∀ t k l, Integrable (fun ω => A (ω t) k l) (pathLaw κ x)) ∧
      (∀ t k, Integrable (fun ω => b (ω t) k) (pathLaw κ x)) ∧
      Summable (fun t => frobNorm ((fun k l => ∫ ω, A (ω t) k l ∂(pathLaw κ x)) -
        fun k l => ∫ y, A y k l ∂ν)) ∧
      ∑' t, frobNorm ((fun k l => ∫ ω, A (ω t) k l ∂(pathLaw κ x)) -
        fun k l => ∫ y, A y k l ∂ν) ≤ C₂ * (1 + euclNorm (f x) ^ q₂) ∧
      Summable (fun t => euclNorm ((fun k => ∫ ω, b (ω t) k ∂(pathLaw κ x)) -
        fun k => ∫ y, b y k ∂ν)) ∧
      ∑' t, euclNorm ((fun k => ∫ ω, b (ω t) k ∂(pathLaw κ x)) -
        fun k => ∫ y, b y k ∂ν) ≤ C₂ * (1 + euclNorm (f x) ^ q₂)) :
    ∃ rstar : Fin K → ℝ,
      (fun k l => ∫ x, A x k l ∂ν) *ᵥ rstar + (fun k => ∫ x, b x k ∂ν) = 0 ∧
      (∀ r : Fin K → ℝ, (fun k l => ∫ x, A x k l ∂ν) *ᵥ r + (fun k => ∫ x, b x k ∂ν) = 0 →
        r = rstar) ∧
      ∀ (x : 𝒳) (r₀ : Fin K → ℝ), ∀ᵐ ω ∂(pathLaw κ x),
        Tendsto (fun t => saIter γ A b r₀ ω t) atTop (𝓝 rstar) := by sorry

end TDApprox.Conv
