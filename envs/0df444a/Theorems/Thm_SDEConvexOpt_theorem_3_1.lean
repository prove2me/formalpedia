-- Prove2me | Theorems.Thm_SDEConvexOpt_theorem_3_1
-- name    : SDEConvexOpt.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:41.468983+00:00
-- url     : https://prove2.me/theorems/0c2ac3d1-7219-4dd7-bc04-c47f360bf1ba
-- title:
--   Theorem 3.1 — the gradient SDE is well posed in every $S^\nu_d$ and, if $\sigma_\infty\in L^2$, converges a.s. to an $\mathcal S$-valued random variable
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ satisfy (H0) (convex, $C^1$, $L$-Lipschitz gradient, $\mathcal S=\operatorname{argmin} f\neq\emptyset$) and $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ satisfy (H) (measurable, bounded entries, Lipschitz in $x$ uniformly in $t$). Let $W$ be an $m$-dimensional Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on $(\Omega,\mathcal F,\mathbb P)$ and $X_0\in\mathbb R^d$, and consider
--   $$
--   dX(t)=-\nabla f(X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad X(0)=X_0. \tag{SDE}
--   $$
--
--   1. **Existence.** If $\mathcal F_0$ contains the $\mathbb P$-null events, (SDE) has a solution $X$ with $\mathbb E\sup_{t\le T}\|X(t)\|^\nu<\infty$ for every $T\ge0$ and every $\nu\ge2$.
--   2. **Uniqueness.** Any two solutions in $S^2_d$ are indistinguishable.
--   3. **Convergence.** If moreover $\int_0^\infty\sigma_\infty(t)^2\,dt<\infty$, where $\sigma_\infty(t)=\sup_x\|\sigma(t,x)\|_F$, then every solution $X$ in $S^2_d$ satisfies:
--      - (i) $\sup_{t\ge0}\mathbb E[\|X(t)\|^2]<+\infty$;
--      - (ii) for every $x^\star\in\mathcal S$, $\lim_{t\to\infty}\|X(t)-x^\star\|$ exists a.s., and $\sup_{t\ge0}\|X(t)\|<+\infty$ a.s.;
--      - (iii) $\lim_{t\to\infty}\|\nabla f(X(t))\|=0$ a.s., and as a result $\lim_{t\to\infty}f(X(t))=\min f$ a.s.;
--      - (iv) there is an $\mathcal S$-valued random variable $x^\star$ with $\lim_{t\to\infty}X(t)=x^\star$ a.s.
--
--   This is the paper's first main result: with noise vanishing in $L^2$, the stochastic gradient flow converges almost surely to a minimizer, as the deterministic gradient flow does.
--
--   Differences from the source:
--   - reading: W is "the m-dimensional Brownian motion" on $(\Omega,\mathcal F,\{\mathcal F_t\},\mathbb P)$ (p.2); "a $\mathcal F_t$-adapted m-dimensional Brownian Motion" (A.1), p.34 → `IsFBrownian`: a standard m-dimensional Brownian motion, adapted to $\mathcal F$, with $W(t)-W(s)$ independent of $\mathcal F_s$ for $s\le t$; reason: the standard meaning of a Brownian motion with respect to a filtration; with adaptedness alone the stochastic integrals of p.10 need not be martingales and the cited existence theorems do not apply
--   - reading: initial condition $X_0$ → a deterministic $X_0\in\mathbb R^d$; reason: p.2 gives (GF) the initial condition $X_0\in\mathbb R^d$, and the proof of (i), p.10, uses $\|X_0-x^\star\|^2/2$ outside every expectation
--   - reading: no condition on the filtered probability space (pp.2, 7) → existence assumes `F0Complete`: $\mathcal F_0$ contains the $\mathbb P$-null events; uniqueness and (i)–(iv) do not; reason: the existence part comes from Theorem A.7, whose cited sources [33], [35] work under the usual conditions; without completeness an adapted solution with continuous paths need not exist
--   - reading: "there exists a unique solution $X\in S^\nu_d$ of (SDE), for every $\nu\ge2$" → a solution exists and lies in $S^\nu_d$ for every real $\nu\ge2$; any two solutions in $S^2_d$ are indistinguishable; reason: $S^\nu_d\subset S^2_d$ for $\nu\ge2$, so uniqueness in $S^2_d$ is the strongest literal reading; $S^\nu_d$ is a quotient by indistinguishability (p.7)
--   - encoding: solutions are progressively measurable processes with almost surely continuous paths, taken modulo indistinguishability (the relation $\mathcal R$ and $S^0_d$, p.7) → `SolvesSDE`: adapted processes with every path continuous, the integral equation outside one null set; reason: adapted plus continuous gives progressive measurability; when $\mathcal F_0$ contains the null sets every class of $S^0_d$ has such a representative, and every conclusion is invariant under indistinguishability
--   - encoding: (i)–(iv) for "the" solution → (i)–(iv) for every solution in $S^2_d$; reason: the same, by the uniqueness clause
--   - encoding: "an $\mathcal S$-valued random variable $x^\star$" → a measurable $x^\star:\Omega\to\mathbb R^d$ with $x^\star(\omega)\in\mathcal S$ for every $\omega$; reason: the definition of a random variable with values in $\mathcal S$
--   - encoding: $\mathbb R^d$, $\mathbb R^{d\times m}$ with $\|\cdot\|_F$, $t\ge0$, expectations, $\sigma_\infty\in L^2(\mathbb R_+)$, $\min f$ → `SDEState d`, `Diffusion d m` (Euclidean norm on $d\times m$ entries = Frobenius), `ℝ≥0`, lower Lebesgue integrals in `ℝ≥0∞`, `SigmaInfL2`, `⨅ x, f x`; reason: Lean conventions; the same instances (all integrands are nonnegative, and $\min f=\inf f$ since $\mathcal S\neq\emptyset$)
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem 3.1, p.9

import Definitions.Def_SDEConvexOpt_F0Complete
import Definitions.Def_SDEConvexOpt_H0
import Definitions.Def_SDEConvexOpt_HypH
import Definitions.Def_SDEConvexOpt_IsFBrownian
import Definitions.Def_SDEConvexOpt_SolvesSDE
import Definitions.Def_SDEConvexOpt_InS
import Definitions.Def_SDEConvexOpt_SigmaInfL2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

open EthierKurtz

/-- Theorem 3.1 of Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex
optimization, arXiv:2207.02750v1, p.9: consider the dynamic (SDE)
`dX(t) = −∇f(X(t)) dt + σ(t, X(t)) dW(t)`, `X(0) = X₀`, where `f` and `σ` satisfy (H0) and (H).
Then there exists a unique solution `X ∈ S^ν_d` of (SDE), for every `ν ≥ 2`. Additionally, if
`σ∞ ∈ L²(ℝ₊)`, then:
(i) `sup_{t ≥ 0} 𝔼[‖X(t)‖²] < +∞`;
(ii) `∀ x⋆ ∈ S`, `lim_{t→∞} ‖X(t) − x⋆‖` exists a.s., and `sup_{t ≥ 0} ‖X(t)‖ < +∞` a.s.;
(iii) `lim_{t→∞} ‖∇f(X(t))‖ = 0` a.s., and as a result `lim_{t→∞} f(X(t)) = min f` a.s.;
(iv) there exists an `S`-valued random variable `x⋆` such that `lim_{t→∞} X(t) = x⋆` a.s.

**Formalization Note** `ℝ^d` is `SDEState d`, matrices are `Diffusion d m` (Frobenius norm), time
is `ℝ≥0`, `W` is an `𝓕`-Brownian motion (`IsFBrownian`) and `X₀ ∈ ℝ^d` is deterministic.
Existence assumes that `𝓕₀` contains the `ℙ`-null sets (`F0Complete`); the solution lies in
`S^ν_d` for every real `ν ≥ 2`. Uniqueness is up to indistinguishability among solutions in
`S²_d`. (i)–(iv) are stated for every solution in `S²_d` (equivalently, by uniqueness, for the
solution). Expectations are lower Lebesgue integrals in `ℝ≥0∞`; `min f` is `⨅ x, f x`; "the limit
exists" means a finite real limit; the random variable of (iv) is measurable and `S`-valued at
every `ω`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsFBrownian P ℱ W) (X₀ : SDEState d)
    (f : SDEState d → ℝ) (L : ℝ≥0) (hf : H0 f L)
    (σ : ℝ≥0 × SDEState d → Diffusion d m) (hσ : HypH σ) :
    (F0Complete P ℱ → ∃ X : ℝ≥0 → Ω → SDEState d,
      SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X ∧ ∀ ν : ℝ, 2 ≤ ν → InS ν P X) ∧
    (∀ X Y : ℝ≥0 → Ω → SDEState d,
      SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X → InS 2 P X →
      SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ Y → InS 2 P Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) ∧
    (SigmaInfL2 σ → ∀ X : ℝ≥0 → Ω → SDEState d,
      SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X → InS 2 P X →
        (⨆ t : ℝ≥0, ∫⁻ ω, ‖X t ω‖ₑ ^ 2 ∂P) < ∞ ∧
        (∀ xs ∈ argminSet f, ∀ᵐ ω ∂P, ∃ ℓ : ℝ, Tendsto (fun t => ‖X t ω - xs‖) atTop (𝓝 ℓ)) ∧
        (∀ᵐ ω ∂P, BddAbove (Set.range fun t => ‖X t ω‖)) ∧
        (∀ᵐ ω ∂P, Tendsto (fun t => ‖gradient f (X t ω)‖) atTop (𝓝 0)) ∧
        (∀ᵐ ω ∂P, Tendsto (fun t => f (X t ω)) atTop (𝓝 (⨅ x, f x))) ∧
        ∃ xs : Ω → SDEState d, Measurable xs ∧ (∀ ω, xs ω ∈ argminSet f) ∧
          ∀ᵐ ω ∂P, Tendsto (fun t => X t ω) atTop (𝓝 (xs ω))) := by sorry

end SDEConvexOpt
