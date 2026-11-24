-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_theorem_7_1
-- name    : PDSmooth.Framework.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:58:39.668067+00:00
-- url     : https://prove2.me/theorems/c0cb4b13-3ae3-4cbe-8f8c-a46d5bcf4b7d
-- title:
--   Theorem 7.1, p. 33 (corrected: λ ∈ (0, (2γ)⁻¹] instead of (0, γ⁻¹)) — Algorithm 3 outputs an ε-NS point in expectation: E‖x_out − prox(q, x_out, λ)‖ ≤ ελ/β_X
-- statement:
--   Assume the standing assumptions of problem (1.1) (base mission). Fix $\varepsilon>0$ and $\lambda$ with $0<\lambda\le(2\gamma)^{-1}$, a starting point $x_1\in\mathcal X$, and any $\Delta_q(x_1)\ge q(x_1)-q^*$. Let
--
--   $$
--   \eta=\varepsilon^2\lambda/(12\beta_{\mathcal X}^2)\qquad\text{and}\qquad K\ \ge\ 8\beta_{\mathcal X}^2\Delta_q(x_1)/(\lambda\varepsilon^2),\ K\ge1\text{ an integer}. \tag{7.5}
--   $$
--
--   Consider a run of Algorithm 3 for $K$ iterations (with $\rho=\eta/(4R_{\mathcal Y}(\omega_{\mathcal Y}))$), and let $x_{\mathrm{out}}=x_\kappa$ with $\kappa$ uniform on $\{1,\dots,K\}$ and independent of the iterates. Then $\|x_{\mathrm{out}}-\operatorname{prox}(q,x_{\mathrm{out}},\lambda)\|$ is integrable and
--
--   $$
--   \mathbb E\big[\|x_{\mathrm{out}}-\operatorname{prox}(q,x_{\mathrm{out}},\lambda)\|\big]\ \le\ \varepsilon\lambda/\beta_{\mathcal X}.
--   $$
--
--   So the output is an $\varepsilon$-near-stationary point of (1.1) in expectation; it is the stochastic counterpart of Theorem 4.1.
--
--   **Formalization Note** *Correction.* The page states $\lambda\in(0,\gamma^{-1})$. The proof (Appendix I, (I.2)) uses $(2\lambda)^{-1}$-strong convexity of $Q^\lambda(\cdot;x_k)$, which is only $(\lambda^{-1}-\gamma)$-strongly convex, and $\lambda^{-1}-\gamma\ge(2\lambda)^{-1}$ exactly when $\lambda\le(2\gamma)^{-1}$. The printed statement is false for $\gamma\lambda>5/6$: take $\mathbb X=\mathbb Y=\mathbb R$, $\mathcal X=[-2,2]$, $\omega_{\mathcal X}=x^2/2$ ($\beta_{\mathcal X}=1$), $\mathcal Y=[0,1]$, $\Phi(x,y)=-x^2/2$ ($\gamma=1$), $g=0$, $\omega_{\mathcal Y}=y^2/2$, $r=0$ on $\mathcal X$, $\lambda=0.9$, $\varepsilon=1$. Then $\eta=0.075$, $\operatorname{prox}(q,x,\lambda)=10x$ and $Q^\lambda(x;x)-q^\lambda(x)=4.5x^2$; with $x_1=\sqrt{1/60}\approx0.1291$ the constant run $x_k\equiv x_1$ satisfies Step 2 with equality, $\Delta_q=2.25\ge q(x_1)-q^*\approx1.9917$ gives $K=20$, and $\mathbb E\|x_{\mathrm{out}}-\operatorname{prox}\|=9x_1\approx1.1619>0.9=\varepsilon\lambda/\beta_{\mathcal X}$. The Lean statement takes $0<\lambda\le(2\gamma)^{-1}$; the range $((2\gamma)^{-1},\gamma^{-1})$ is excluded (between $(2\gamma)^{-1}$ and $(6\gamma/5)^{-1}$ the statement is neither proved nor refuted). *Other conventions.* $q^*$ enters only through $\Delta_q$, stated as $q(x_1)-q(z)\le\Delta_q$ for all $z\in\mathcal X$. The prox point is any selection $p$ with $p(z)=\operatorname{prox}(q,z,\lambda)$ for $z\in\mathcal X$ (it is unique there). The Bochner integral is used together with an integrability claim, so the bound cannot hold by a junk value.
--
--   Differences from the source:
--   - correction: λ ∈ (0, γ⁻¹) → 0 < λ ≤ (2γ)⁻¹; reason: false as printed for γλ > 5/6: the 1-D instance X = [−2,2], ω_X = x²/2, Φ = −x²/2, Y = [0,1], g = 0, ω_Y = y²/2, r = 0, γ = 1, λ = 0.9, ε = 1, x_k ≡ 0.1291, Δ_q = 2.25, K = 20 gives E‖x_out − prox‖ = 1.1619 > 0.9; the proof's (I.2) needs λ⁻¹ − γ ≥ (2λ)⁻¹, i.e. λ ≤ (2γ)⁻¹
--   - generalization: K = 8β²_XΔ_q(x₁)/(λε²) (a real number) → any integer K ≥ 1 with K ≥ 8β²_XΔ_q(x₁)/(λε²); reason: the run needs an integer number of iterations; whenever the page's K is a positive integer it is an admissible K, and the proof (I.6)–(I.7) only uses the inequality
--   - encoding: Δ_q(x₁) ≥ q(x₁) − q* with q* = inf_X q → ∀ z ∈ X, q(x₁) − q(z) ≤ Δ_q; reason: equivalent for the infimum q*
--   - encoding: random iterates with E[Q^λ_ρ(x_{k+1};x_k) | x_k] ≤ q^λ_ρ(x_k) + η → measurable iterates, integrable Q^λ_ρ(x_{k+1};x_k), and the conditional expectation given σ(x_k) bounded a.s. by Q^λ_ρ(x′;x_k) + η for every x′ ∈ X; reason: Lean's conditional expectation needs integrability and measurability, which the page's expectation presupposes; the infimum is written against every x′ inside the almost-sure statement
--   - encoding: x_out = x_k with k ∼ Unif{1,…,K} → x_out(ω) = x_{κ(ω)}(ω) with κ measurable, P(κ = k) = 1/K for k ∈ {1,…,K}, and κ independent of (x_k)_k; reason: the page samples the output index independently of the run
--   - encoding: prox(q, x_out, λ) → p(x_out) for any p with IsProx q ω_X X λ z (p z) for all z ∈ X; reason: the prox point is unique on X, so p is the prox map there
--   - encoding: E[‖x_out − prox(q, x_out, λ)‖] ≤ ελ/β_X → integrability of ‖x_out − p(x_out)‖ and the Bochner-integral bound; reason: excludes the junk value 0 of a non-integrable function
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 33, Theorem 7.1, (7.5) (Algorithm 3, p. 34; proof Appendix I, pp. 43–44)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Definitions.Def_PDSmooth_Framework_Supplement_Alg3

namespace PDSmooth.Framework.Supplement

open MeasureTheory ProbabilityTheory PDSmooth.Framework

/-- Theorem 7.1, p. 33, corrected: the page states `λ ∈ (0, γ⁻¹)`, but the statement is false for
`γλ > 5/6` (see the Formalization Note of the item); it is stated for `0 < λ ≤ (2γ)⁻¹`, the range on
which the proof's (I.2) is valid. Fix `ε > 0`. For a run of Algorithm 3 from `x₁ ∈ X` with
`η = ε²λ/(12β²_X)`, `K` iterations, `K ≥ 8β²_XΔ_q(x₁)/(λε²)` where `Δ_q(x₁) ≥ q(x₁) − q*`, and output
`x_out = x_κ` with `κ ∼ Unif{1,…,K}` independent of the iterates, `‖x_out − prox(q, x_out, λ)‖` is
integrable and `E[‖x_out − prox(q, x_out, λ)‖] ≤ ελ/β_X`. -/
theorem theorem_7_1 {E F Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ε lam η Δq : ℝ) (K : ℕ) (x1 : E) (x : ℕ → Ω → E) (κ : Ω → ℕ) (p : E → E)
    (hε : 0 < ε) (hlam0 : 0 < lam) (hlam1 : lam ≤ (2 * γ)⁻¹)
    (hΔ : ∀ z ∈ X, qObj Φ g r Y x1 - qObj Φ g r Y z ≤ Δq)
    (hη : η = ε ^ 2 * lam / (12 * βX ^ 2))
    (hK1 : 1 ≤ K) (hK : 8 * βX ^ 2 * Δq / (lam * ε ^ 2) ≤ (K : ℝ))
    (hrun : IsAlg3Run P X Y Φ g r ωX ωY lam η K x1 x)
    (hκ : IsUniformIndex P κ K) (hind : IndepFun κ (fun ω k => x k ω) P)
    (hp : ∀ z ∈ X, IsProx (qObj Φ g r Y) ωX X lam z (p z)) :
    Integrable (fun ω => ‖x (κ ω) ω - p (x (κ ω) ω)‖) P ∧
      ∫ ω, ‖x (κ ω) ω - p (x (κ ω) ω)‖ ∂P ≤ ε * lam / βX := by sorry

end PDSmooth.Framework.Supplement
