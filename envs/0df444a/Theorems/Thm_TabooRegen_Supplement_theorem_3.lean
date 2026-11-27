-- Prove2me | Theorems.Thm_TabooRegen_Supplement_theorem_3
-- name    : TabooRegen.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:44:50.931751+00:00
-- url     : https://prove2.me/theorems/6b4812e6-c7a4-4d4e-8f69-7a11dd70116d
-- title:
--   Theorem 3 — CLT and large deviations of $C(t)$ given $\Gamma^\circ>t$ (corrected: A9′ near $(0,\alpha)$, rates $-\theta_xx+\kappa(\theta_x)+\alpha$, (5.5) near $\mu$, $\sigma^2>0$ for (5.4)–(5.5))
-- statement:
--   Let $X$ be **classically regenerative** (Definition 1) with $T(0)=0$, let $A\subseteq S$ with exit time $\Gamma=\Gamma^\circ$, and let $f:S\to\mathbb R$ be Borel measurable with additive functional $C(t)=\int_0^tf(X(s))\,ds$. Let $Y_1=\int_0^{\tau_1}f(W_1(s))\,ds$, $\varphi(\theta_1,\theta_2)=E[\exp(\theta_1Y_1+\theta_2\tau_1);\Gamma^\circ\ge\tau_1]$, and let $\mu$ and $\sigma^2$ be the tilted cycle mean and variance
--   $$
--   \mu=\frac{E[Y_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}{E[\tau_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]},\qquad
--   \sigma^2=\frac{E[(Y_1-\mu\tau_1)^2e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}{E[\tau_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}.
--   $$
--   Assume A1 (with $\alpha\ge0$), A2, and the moment condition
--
--   **A9′.** $E\exp\big(\theta_1\int_0^{\tau_1\wedge\Gamma^\circ}|f(X(u))|\,du+\theta_2(\tau_1\wedge\Gamma^\circ)\big)<\infty$ for $(\theta_1,\theta_2)$ in a neighbourhood of $(0,\alpha)$.
--
--   Then:
--
--   1. **Central limit theorem (5.3).** As $t\to\infty$,
--   $$
--   P\big(t^{-1/2}(C(t)-\mu t)\le y\mid\Gamma^\circ>t\big)\to P(\sigma N(0,1)\le y)
--   $$
--   at every continuity point $y$ of the limit (every $y$ if $\sigma>0$, every $y\ne0$ if $\sigma=0$).
--
--   2. **Large deviations (5.4)–(5.5).** Suppose $\sigma^2>0$. There are $\delta>0$, a function $\kappa$ with $\varphi(\theta,-\kappa(\theta))=1$ for $|\theta|<\delta$, and $\eta>0$ such that, for every $x\in(\mu,\mu+\eta)$, some $\theta_x\in(-\delta,\delta)$ has $\kappa'(\theta_x)=x$, and for every such $\theta_x$
--   $$
--   \frac1t\log P\big(C(t)>xt\mid\Gamma^\circ>t\big)\to-\theta_xx+\kappa(\theta_x)+\alpha;
--   $$
--   and, for every $x\in(\mu-\eta,\mu)$, some $\theta_x\in(-\delta,\delta)$ has $\kappa'(\theta_x)=x$, and for every such $\theta_x$
--   $$
--   \frac1t\log P\big(C(t)<xt\mid\Gamma^\circ>t\big)\to-\theta_xx+\kappa(\theta_x)+\alpha.
--   $$
--   The conditional probabilities are positive for all large $t$.
--
--   The theorem describes the fluctuations of a cumulative reward accumulated over a long tabooed horizon: given that the process has not left $A$, $C(t)$ grows at rate $\mu$ (the reward rate of the tilted cycle law, not of the unconditioned process), with Gaussian fluctuations of order $\sqrt t$ and exponentially small probabilities of order $e^{-tI(x)}$ for deviations of order $t$, with $I(x)=\theta_xx-\kappa(\theta_x)-\alpha$.
--
--   This is a **corrected** version of the printed theorem, which is false as stated: see the corrections below.
--
--   Differences from the source:
--   - encoding: complete separable metric space $S$, paths in $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → Polish $S$ with its Borel σ-algebra; the published `Path S` (càdlàg maps into `S ⊕ Unit`, cylinder-trace σ-algebra); reason: the convention of the published `TabooRegen.Model`; the cylinder trace equals the Skorohod Borel σ-algebra for separable metric $\tilde S$
--   - correction: A9: $E[\exp(\theta_1\int_0^{\tau_1}|f(X(T(0)+u))|du+\theta_2\tau_1);\Gamma^\circ\ge\tau_1]<\infty$ for $(\theta_1,\theta_2)$ near $(0,0)$ → A9′: $E\exp(\theta_1\int_0^{\tau_1\wedge\Gamma^\circ}|f(X(u))|du+\theta_2(\tau_1\wedge\Gamma^\circ))<\infty$ for $(\theta_1,\theta_2)$ near $(0,\alpha)$; reason: as printed (5.3) fails: a four-state classically regenerative process with $\alpha=1/2$, $\mu=0$ satisfying A1, A2 and A9 has $C(t)/t\to1$ given $\Gamma>t$, because A9 does not control the cycle in progress; and A9 does not make $\varphi$ finite near $(0,\alpha)$ (an example with $\sigma^2=\infty$ where $\kappa(\theta)$ exists for no $\theta\ne0$); A9′ is what the proof step "Using A9, it is straightforward…" (p.293) needs; A9′ implies A9 under A1 and equals it at $\alpha=0$; it excludes, for $\alpha>0$, processes with an infinite tilted or stopped-cycle moment
--   - reading: $\varphi(\theta_x)$, $\varphi'(\theta_x)=x$ (one-variable $\varphi$), $\varphi(0,-\alpha)=1$, $\varphi(0)=-\alpha$ → $\kappa$ pinned by $\varphi(\theta,-\kappa(\theta))=1$ on $(-\delta,\delta)$, `HasDerivAt κ x θ`; reason: the one-variable function is the $\kappa$ of p.292: $\exp(-\varphi(\theta)t)$ normalizes $\tilde G(\theta,\cdot)$ in the proof, and $\kappa(0)=-\alpha$, $\varphi(0,\alpha)=1$ by A1
--   - correction: rate $-\theta_xx+\varphi(\theta_x)$ in (5.4) and $-\theta_x+\varphi(\theta_x)$ in (5.5) → rate $-\theta_xx+\kappa(\theta_x)+\alpha$ in both; reason: the proof ends with $(1/t)\log E[\exp(\theta C(t))\mid\Gamma^\circ>t]\to\varphi(\theta)+\alpha$ (p.293); the printed rate tends to $-\alpha$, not $0$, as $x\to\mu$; example with $\alpha=1/2$, $\kappa(\theta)=-3/4+\sqrt{\theta^2+1/16}$: at $x=0.6$ the rate is $-0.05$, the printed formula gives $-0.55$
--   - correction: (5.5): $x<\mu$ in a neighbourhood of the origin, $P(C(t)<\mu t\mid\Gamma^\circ>t)$ → $x\in(\mu-\eta,\mu)$, $P(C(t)<xt\mid\Gamma^\circ>t)$; reason: the printed left side does not depend on $x$ and tends to $0$ by (5.3) when $\sigma>0$, while the right side varies with $x$; the symmetric reading of (5.4) is the one the Gärtner–Ellis argument gives
--   - correction: (5.4)–(5.5) for every $\sigma\ge0$ → (5.4)–(5.5) under $\sigma^2>0$; (5.3) for every $\sigma\ge0$; reason: $f\equiv0$ satisfies every assumption, has $\kappa'\equiv0$, so no $\theta_x$ with $\kappa'(\theta_x)=x\ne\mu$ exists
--   - encoding: $P(t^{-1/2}(C(t)-\mu t)\le\cdot\mid\Gamma^\circ>t)\Rightarrow P(\sigma N(0,1)\le\cdot)$ → convergence of the conditional distribution functions at every $y$ with $\sigma^2>0$ or $y\ne0$ to the distribution function of `gaussianReal 0 σ²`; reason: these are the continuity points of the limit (the point mass at $0$ when $\sigma=0$); for laws on $\mathbb R$ this is weak convergence
--   - encoding: "for $x>\mu$ (resp. $x<\mu$) in a neighbourhood of $\mu$", "where $\varphi'(\theta_x)=x$", $\frac1t\log P(\cdot)$ → explicit radii $\delta>0$ (for $\theta$, where $\kappa$ is pinned) and $\eta>0$ (for $x$), existence of $\theta_x\in(-\delta,\delta)$ with $\kappa'(\theta_x)=x$ and the limit for every such $\theta_x$; the conditional probabilities are eventually positive; reason: $\kappa$ is defined only near $0$; a negative limit of $\frac1t\log P$ already forces eventual positivity, and stating it keeps `Real.log` away from its junk value at $0$
--   - encoding: $\Gamma^\circ$, expectations $E$, $C(t)$, $Y_1$, $\mu$, $\sigma^2$ → $\Gamma$ and $P$ (since $T(0)=0$); Bochner integrals for $C(t)$, $Y_1$, $\mu$, $\sigma^2$; published A1, A2 under $Q$; reason: with $T(0)=0$, $\Gamma^\circ=\Gamma$ and $Q=P$; under A1 and A9′ the integrands are integrable, so the Bochner values are the true ones
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 3, p.293 (PDF p.23); definitions p.292; proof pp.293–294

import Mathlib
import Definitions.Def_TabooRegen_Supplement_Additive

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.Supplement

open TabooRegen TabooRegen.Model

/-- **Theorem 3** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing
Systems 46 (2004), p.293), **corrected**. Let `X` be classically regenerative with `T(0) = 0`, let
`f : S → ℝ` be Borel, and assume A1, A2 and `A9′`. Then
1. (5.3) `P(t^{−1/2}(C(t) − µt) ⩽ y | Γ° > t) → P(σN(0, 1) ⩽ y)` at every continuity point `y` of the
   limit;
2. if `σ² > 0`, there are `δ > 0` and `κ` with `ϕ(θ, −κ(θ)) = 1` for `|θ| < δ`, and `η > 0`, such
   that for `x ∈ (µ, µ + η)` (5.4) and for `x ∈ (µ − η, µ)` (5.5) there is `θ_x` with `|θ_x| < δ` and
   `κ′(θ_x) = x`, and for every such `θ_x`
   `(1/t) log P(C(t) > xt | Γ° > t) → −θ_x x + κ(θ_x) + α`, resp.
   `(1/t) log P(C(t) < xt | Γ° > t) → −θ_x x + κ(θ_x) + α`.

**Formalization Note.**
* Corrections (false as printed; counterexamples in the mission notes): the printed A9 (moments
  of completed tabooed cycles near `(0, 0)`) is replaced by `A9′` (moments of the stopped cycle
  `[0, τ₁ ∧ Γ°)` near `(0, α)`), which the proof's step "Using A9, …" needs; the one-variable `ϕ` of
  (5.4)–(5.5) is `κ`; both rates carry `+ α` (the last display of the proof); (5.5) is read with `x`
  near `µ`, `C(t) < xt` and `−θ_x x`; `σ² > 0` is assumed for (5.4)–(5.5) only.
* `Γ° = Γ` and `Q = P` because `T(0) = 0`.
* (5.3) is convergence of distribution functions at the continuity points of the `N(0, σ²)` law
  (`gaussianReal 0 σ²`, the point mass at `0` when `σ = 0`); for laws on `ℝ` this is weak
  convergence.
* `κ` is pinned by `ϕ(θ, −κ(θ)) = 1` on `(−δ, δ)` (it is unique there because `τ₁ > 0`); `κ′(θ_x) = x`
  is `HasDerivAt κ x θ_x`. The neighbourhood `(µ − η, µ + η)` of `x` ("in a neighborhood of `µ`") has
  its own radius `η`: `κ′` maps `(−δ, δ)` onto roughly `(µ − σ²δ, µ + σ²δ)`, so tying `η` to `δ` would be
  false whenever `σ² < 1`. The conditional probabilities in (5.4)–(5.5) are asserted to be
  eventually positive, so `Real.log` is never applied to `0`. -/
theorem theorem_3 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hcl : IsClassicallyRegen M) (h0 : ∀ ω, M.T 0 ω = 0) (f : S → ℝ) (hf : Measurable f)
    {α : ℝ} (h1 : M.A1 α) (h2 : M.A2) (h9 : A9' M f α) :
    (∀ y : ℝ, (0 < sigma2 M f α ∨ y ≠ 0) →
      Tendsto (fun t : ℝ => (ProbabilityTheory.cond M.P {ω | ENNReal.ofReal t < M.Γ ω}
          {ω | (C M f t ω - mu M f α * t) / Real.sqrt t ≤ y}).toReal) atTop
        (𝓝 (ProbabilityTheory.gaussianReal 0 (sigma2 M f α).toNNReal (Set.Iic y)).toReal)) ∧
    (0 < sigma2 M f α → ∃ δ > 0, ∃ κ : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo (-δ) δ, phi M f θ (-κ θ) = 1) ∧ ∃ η > 0,
      (∀ x ∈ Set.Ioo (mu M f α) (mu M f α + η),
        (∃ θ ∈ Set.Ioo (-δ) δ, HasDerivAt κ x θ) ∧
        ∀ θ ∈ Set.Ioo (-δ) δ, HasDerivAt κ x θ →
          (∀ᶠ t in atTop, 0 < ProbabilityTheory.cond M.P {ω | ENNReal.ofReal t < M.Γ ω}
            {ω | x * t < C M f t ω}) ∧
          Tendsto (fun t : ℝ => Real.log (ProbabilityTheory.cond M.P
              {ω | ENNReal.ofReal t < M.Γ ω} {ω | x * t < C M f t ω}).toReal / t) atTop
            (𝓝 (-θ * x + κ θ + α))) ∧
      (∀ x ∈ Set.Ioo (mu M f α - η) (mu M f α),
        (∃ θ ∈ Set.Ioo (-δ) δ, HasDerivAt κ x θ) ∧
        ∀ θ ∈ Set.Ioo (-δ) δ, HasDerivAt κ x θ →
          (∀ᶠ t in atTop, 0 < ProbabilityTheory.cond M.P {ω | ENNReal.ofReal t < M.Γ ω}
            {ω | C M f t ω < x * t}) ∧
          Tendsto (fun t : ℝ => Real.log (ProbabilityTheory.cond M.P
              {ω | ENNReal.ofReal t < M.Γ ω} {ω | C M f t ω < x * t}).toReal / t) atTop
            (𝓝 (-θ * x + κ θ + α)))) := by sorry

end TabooRegen.Supplement
