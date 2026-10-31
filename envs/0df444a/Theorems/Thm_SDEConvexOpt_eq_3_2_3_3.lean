-- Prove2me | Theorems.Thm_SDEConvexOpt_eq_3_2_3_3
-- name    : SDEConvexOpt.eq_3_2_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:19.534507+00:00
-- url     : https://prove2.me/theorems/07bf1d85-2ff4-432c-895f-e6604de3b9bc
-- title:
--   Displays (3.2)–(3.3) — $\int_0^\infty\langle\nabla f(X),X-x^\star\rangle<\infty$ a.s. and $\lim\|X(t)-x^\star\|$ exists a.s.
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ satisfy (H0) (convex, $C^1$, with $L$-Lipschitz gradient, and $\mathcal S=\operatorname{argmin} f\neq\emptyset$) and let $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ satisfy (H) (measurable, with bounded entries that are $l_0$-Lipschitz in $x$ uniformly in $t$). Let $W$ be an $m$-dimensional Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, let $X_0\in\mathbb R^d$, and let $X$ be a solution of
--   $$
--   dX(t)=-\nabla f(X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad X(0)=X_0, \tag{SDE}
--   $$
--   lying in $S^2_d$, i.e. $\mathbb E\big(\sup_{t\in[0,T]}\|X(t)\|^2\big)<\infty$ for every $T\ge0$. Assume moreover that the noise is square integrable in time: with $\sigma_\infty(t)=\sup_{x\in\mathbb R^d}\|\sigma(t,x)\|_F$, $\int_0^\infty\sigma_\infty(t)^2\,dt<\infty$. Let $x^\star\in\mathcal S$. Then
--   $$
--   \int_0^\infty\langle\nabla f(X(s)),X(s)-x^\star\rangle\,ds<+\infty\quad\text{a.s.,} \tag{3.2}
--   $$
--   and there is an event $\Omega_{x^\star}$ with $\mathbb P(\Omega_{x^\star})=1$ on which $\lim_{t\to\infty}\|X(\omega,t)-x^\star\|$ exists (and is finite). (3.3)
--
--   These are the two outputs of Theorem A.9 used for parts (ii) and (iii) of Theorem 3.1.
--
--   Differences from the source:
--   - reading: W is "the m-dimensional Brownian motion" on $(\Omega,\mathcal F,\{\mathcal F_t\},\mathbb P)$ (p.2); "a $\mathcal F_t$-adapted m-dimensional Brownian Motion" (A.1), p.34 → `IsFBrownian`: a standard m-dimensional Brownian motion, adapted to $\mathcal F$, with $W(t)-W(s)$ independent of $\mathcal F_s$ for $s\le t$; reason: the standard meaning of a Brownian motion with respect to a filtration; with adaptedness alone the stochastic integrals of p.10 need not be martingales and the cited existence theorems do not apply
--   - reading: initial condition $X_0$ → a deterministic $X_0\in\mathbb R^d$; reason: p.2 gives (GF) the initial condition $X_0\in\mathbb R^d$, and the proof of (i), p.10, uses $\|X_0-x^\star\|^2/2$ outside every expectation
--   - encoding: solutions are progressively measurable processes with almost surely continuous paths, taken modulo indistinguishability (the relation $\mathcal R$ and $S^0_d$, p.7) → `SolvesSDE`: adapted processes with every path continuous, the integral equation outside one null set; reason: adapted plus continuous gives progressive measurability; when $\mathcal F_0$ contains the null sets every class of $S^0_d$ has such a representative, and every conclusion is invariant under indistinguishability
--   - encoding: "the" solution of (SDE) → every solution of (SDE) in $S^2_d$; reason: Theorem 3.1 makes the solution unique in $S^2_d$ up to indistinguishability, and the conclusion is invariant under indistinguishability
--   - encoding: $\int_0^\infty\langle\nabla f(X(s)),X(s)-x^\star\rangle ds<+\infty$ → lower Lebesgue integral over $[0,\infty)$ of `ENNReal.ofReal` of the integrand is finite; reason: the integrand is nonnegative by convexity, so this is the same quantity
--   - encoding: $\exists\Omega_{x^\star}\in\mathcal F$, $\mathbb P(\Omega_{x^\star})=1$, the limit exists on it → `∀ᵐ ω ∂P`, a finite real limit exists; reason: the same statement
--   - encoding: $\mathbb R^d$, $\mathbb R^{d\times m}$ with $\|\cdot\|_F$, $t\ge0$, expectations, $\sigma_\infty\in L^2(\mathbb R_+)$, $\min f$ → `SDEState d`, `Diffusion d m` (Euclidean norm on $d\times m$ entries = Frobenius), `ℝ≥0`, lower Lebesgue integrals in `ℝ≥0∞`, `SigmaInfL2`, `⨅ x, f x`; reason: Lean conventions; the same instances (all integrands are nonnegative, and $\min f=\inf f$ since $\mathcal S\neq\emptyset$)
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, §3.1, proof of Theorem 3.1(ii), displays (3.2) and (3.3), p.10

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

/-- Displays (3.2) and (3.3) of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.10 (§3.1, proof
of Theorem 3.1(ii), by Theorem A.9): under (H0), (H) and `σ∞ ∈ L²(ℝ₊)`, for every `x⋆ ∈ S`,
`∫₀^∞ ⟨∇f(X(s)), X(s) − x⋆⟩ ds < +∞` almost surely (3.2), and `lim_{t→∞} ‖X(ω, t) − x⋆‖` exists
for `ω` in an event of probability one (3.3).

**Formalization Note** `ℝ^d` is `SDEState d`, matrices are `Diffusion d m` (Frobenius norm), time is `ℝ≥0`, `W` is an
`𝓕`-Brownian motion (`IsFBrownian`), `X₀ ∈ ℝ^d` is deterministic, and `X` is any solution of (SDE)
(`SolvesSDE` with drift `−∇f`) in `S²_d`; by Theorem 3.1 that is the unique solution. The integrand of (3.2) is nonnegative by convexity; its integral
over `[0, ∞)` is a lower Lebesgue integral in `ℝ≥0∞` of `ENNReal.ofReal` of it. "The limit
exists" means a finite real limit. -/
theorem eq_3_2_3_3 {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsFBrownian P ℱ W) (X₀ : SDEState d)
    (f : SDEState d → ℝ) (L : ℝ≥0) (hf : H0 f L)
    (σ : ℝ≥0 × SDEState d → Diffusion d m) (hσ : HypH σ)
    (hL2 : SigmaInfL2 σ)
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X) (hX2 : InS 2 P X)
    (xs : SDEState d) (hxs : xs ∈ argminSet f) :
    (∀ᵐ ω ∂P, ∫⁻ s in Set.Ici (0 : ℝ),
      ENNReal.ofReal ⟪gradient f (X s.toNNReal ω), X s.toNNReal ω - xs⟫_ℝ < ∞) ∧
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ, Tendsto (fun t => ‖X t ω - xs‖) atTop (𝓝 ℓ) := by sorry

end SDEConvexOpt
