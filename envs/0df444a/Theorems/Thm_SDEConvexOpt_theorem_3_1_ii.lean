-- Prove2me | Theorems.Thm_SDEConvexOpt_theorem_3_1_ii
-- name    : SDEConvexOpt.theorem_3_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:24.419702+00:00
-- url     : https://prove2.me/theorems/06d20dfb-301f-4ebb-ae74-95347c87207e
-- title:
--   Theorem 3.1(ii) — $\lim_t\|X(t)-x^\star\|$ exists a.s. for each $x^\star\in\mathcal S$, and $\sup_t\|X(t)\|<\infty$ a.s.
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ satisfy (H0) (convex, $C^1$, with $L$-Lipschitz gradient, and $\mathcal S=\operatorname{argmin} f\neq\emptyset$) and let $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ satisfy (H) (measurable, with bounded entries that are $l_0$-Lipschitz in $x$ uniformly in $t$). Let $W$ be an $m$-dimensional Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, let $X_0\in\mathbb R^d$, and let $X$ be a solution of
--   $$
--   dX(t)=-\nabla f(X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad X(0)=X_0, \tag{SDE}
--   $$
--   lying in $S^2_d$, i.e. $\mathbb E\big(\sup_{t\in[0,T]}\|X(t)\|^2\big)<\infty$ for every $T\ge0$. Assume moreover that the noise is square integrable in time: with $\sigma_\infty(t)=\sup_{x\in\mathbb R^d}\|\sigma(t,x)\|_F$, $\int_0^\infty\sigma_\infty(t)^2\,dt<\infty$.
--
--   Then
--   1. for every $x^\star\in\mathcal S$, $\lim_{t\to\infty}\|X(t)-x^\star\|$ exists (and is finite) almost surely;
--   2. $\sup_{t\ge0}\|X(t)\|<+\infty$ almost surely.
--
--   Differences from the source:
--   - reading: W is "the m-dimensional Brownian motion" on $(\Omega,\mathcal F,\{\mathcal F_t\},\mathbb P)$ (p.2); "a $\mathcal F_t$-adapted m-dimensional Brownian Motion" (A.1), p.34 → `IsFBrownian`: a standard m-dimensional Brownian motion, adapted to $\mathcal F$, with $W(t)-W(s)$ independent of $\mathcal F_s$ for $s\le t$; reason: the standard meaning of a Brownian motion with respect to a filtration; with adaptedness alone the stochastic integrals of p.10 need not be martingales and the cited existence theorems do not apply
--   - reading: initial condition $X_0$ → a deterministic $X_0\in\mathbb R^d$; reason: p.2 gives (GF) the initial condition $X_0\in\mathbb R^d$, and the proof of (i), p.10, uses $\|X_0-x^\star\|^2/2$ outside every expectation
--   - encoding: solutions are progressively measurable processes with almost surely continuous paths, taken modulo indistinguishability (the relation $\mathcal R$ and $S^0_d$, p.7) → `SolvesSDE`: adapted processes with every path continuous, the integral equation outside one null set; reason: adapted plus continuous gives progressive measurability; when $\mathcal F_0$ contains the null sets every class of $S^0_d$ has such a representative, and every conclusion is invariant under indistinguishability
--   - encoding: "the" solution of (SDE) → every solution of (SDE) in $S^2_d$; reason: Theorem 3.1 makes the solution unique in $S^2_d$ up to indistinguishability, and the conclusion is invariant under indistinguishability
--   - encoding: $\mathbb R^d$, $\mathbb R^{d\times m}$ with $\|\cdot\|_F$, $t\ge0$, expectations, $\sigma_\infty\in L^2(\mathbb R_+)$, $\min f$ → `SDEState d`, `Diffusion d m` (Euclidean norm on $d\times m$ entries = Frobenius), `ℝ≥0`, lower Lebesgue integrals in `ℝ≥0∞`, `SigmaInfL2`, `⨅ x, f x`; reason: Lean conventions; the same instances (all integrands are nonnegative, and $\min f=\inf f$ since $\mathcal S\neq\emptyset$)
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem 3.1(ii), p.9

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

/-- Theorem 3.1(ii) of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.9: under (H0), (H) and
`σ∞ ∈ L²(ℝ₊)`, for every `x⋆ ∈ S`, `lim_{t→∞} ‖X(t) − x⋆‖` exists a.s., and
`sup_{t ≥ 0} ‖X(t)‖ < +∞` a.s.

**Formalization Note** `ℝ^d` is `SDEState d`, matrices are `Diffusion d m` (Frobenius norm), time is `ℝ≥0`, `W` is an
`𝓕`-Brownian motion (`IsFBrownian`), `X₀ ∈ ℝ^d` is deterministic, and `X` is any solution of (SDE)
(`SolvesSDE` with drift `−∇f`) in `S²_d`; by Theorem 3.1 that is the unique solution. "The limit exists" means a finite real limit; the a.s. bound is
`BddAbove` of the range of `t ↦ ‖X(t, ω)‖`. -/
theorem theorem_3_1_ii {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsFBrownian P ℱ W) (X₀ : SDEState d)
    (f : SDEState d → ℝ) (L : ℝ≥0) (hf : H0 f L)
    (σ : ℝ≥0 × SDEState d → Diffusion d m) (hσ : HypH σ)
    (hL2 : SigmaInfL2 σ)
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X) (hX2 : InS 2 P X) :
    (∀ xs ∈ argminSet f, ∀ᵐ ω ∂P, ∃ ℓ : ℝ, Tendsto (fun t => ‖X t ω - xs‖) atTop (𝓝 ℓ)) ∧
    ∀ᵐ ω ∂P, BddAbove (Set.range fun t => ‖X t ω‖) := by sorry

end SDEConvexOpt
