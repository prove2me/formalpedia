-- Prove2me | Theorems.Thm_SDEConvexOpt_eq_3_1
-- name    : SDEConvexOpt.eq_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:45.651508+00:00
-- url     : https://prove2.me/theorems/fc08f54c-0f91-4518-8d4b-604f541bd24c
-- title:
--   Display (3.1) and p.10 — Itô's formula for $\|X(t)-x^\star\|^2/2$; $M_t$ is a square-integrable continuous martingale
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ satisfy (H0) (convex, $C^1$, with $L$-Lipschitz gradient, and $\mathcal S=\operatorname{argmin} f\neq\emptyset$) and let $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ satisfy (H) (measurable, with bounded entries that are $l_0$-Lipschitz in $x$ uniformly in $t$). Let $W$ be an $m$-dimensional Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, let $X_0\in\mathbb R^d$, and let $X$ be a solution of
--   $$
--   dX(t)=-\nabla f(X(t))\,dt+\sigma(t,X(t))\,dW(t),\qquad X(0)=X_0, \tag{SDE}
--   $$
--   lying in $S^2_d$, i.e. $\mathbb E\big(\sup_{t\in[0,T]}\|X(t)\|^2\big)<\infty$ for every $T\ge0$. Let $x^\star\in\mathcal S$ and $\Sigma=\sigma\sigma^\top$, so that $\operatorname{tr}\Sigma(s,x)=\|\sigma(s,x)\|_F^2$.
--
--   Then there are real processes $J_1,\dots,J_m$ and $M=\sum_k J_k$ such that
--   1. $J_k(t)=\int_0^t\big(\sigma^\top(s,X(s))(X(s)-x^\star)\big)_k\,dW_k(s)$ is an Itô integral for $(\mathcal F_t)$, so that $M_t=\int_0^t\langle\sigma^\top(s,X(s))(X(s)-x^\star),dW(s)\rangle$;
--   2. $M$ is a martingale for $(\mathcal F_t)$ with $\mathbb E M_t^2<\infty$ for every $t$ and almost surely continuous paths;
--   3. almost surely, for every $t\ge0$,
--   $$
--   \frac{\|X(t)-x^\star\|^2}{2}=\frac{\|X_0-x^\star\|^2}{2}+\frac12\int_0^t\operatorname{tr}\Sigma(s,X(s))\,ds-\int_0^t\langle\nabla f(X(s)),X(s)-x^\star\rangle\,ds+M_t. \tag{3.1}
--   $$
--
--   The decomposition $\xi+A_t-U_t+M_t$ of (3.1) is the input to Theorem A.9 in the proof of Theorem 3.1.
--
--   Differences from the source:
--   - reading: W is "the m-dimensional Brownian motion" on $(\Omega,\mathcal F,\{\mathcal F_t\},\mathbb P)$ (p.2); "a $\mathcal F_t$-adapted m-dimensional Brownian Motion" (A.1), p.34 → `IsFBrownian`: a standard m-dimensional Brownian motion, adapted to $\mathcal F$, with $W(t)-W(s)$ independent of $\mathcal F_s$ for $s\le t$; reason: the standard meaning of a Brownian motion with respect to a filtration; with adaptedness alone the stochastic integrals of p.10 need not be martingales and the cited existence theorems do not apply
--   - reading: initial condition $X_0$ → a deterministic $X_0\in\mathbb R^d$; reason: p.2 gives (GF) the initial condition $X_0\in\mathbb R^d$, and the proof of (i), p.10, uses $\|X_0-x^\star\|^2/2$ outside every expectation
--   - encoding: solutions are progressively measurable processes with almost surely continuous paths, taken modulo indistinguishability (the relation $\mathcal R$ and $S^0_d$, p.7) → `SolvesSDE`: adapted processes with every path continuous, the integral equation outside one null set; reason: adapted plus continuous gives progressive measurability; when $\mathcal F_0$ contains the null sets every class of $S^0_d$ has such a representative, and every conclusion is invariant under indistinguishability
--   - encoding: "the" solution of (SDE) → every solution of (SDE) in $S^2_d$; reason: Theorem 3.1 makes the solution unique in $S^2_d$ up to indistinguishability, and the conclusion is invariant under indistinguishability
--   - encoding: $\int_0^t\langle\sigma^\top(s,X(s))(X(s)-x^\star),dW(s)\rangle$ → $\sum_k J_k$ with each $J_k$ a `HasBrownianItoIntegral` of $\sum_i\sigma_{ik}(s,X(s))(X_i(s)-x^\star_i)$ against $W_k$; reason: the definition of the vector stochastic integral
--   - encoding: $\operatorname{tr}\Sigma(s,X(s))$ with $\Sigma=\sigma\sigma^\top$ (p.9) → $\|\sigma(s,X(s))\|^2$, the squared Frobenius norm; reason: $\operatorname{tr}(\sigma\sigma^\top)=\|\sigma\|_F^2$
--   - encoding: "continuous" martingale → continuous paths almost surely; reason: the paper's definition of a continuous process, p.7
--   - encoding: $\mathbb R^d$, $\mathbb R^{d\times m}$ with $\|\cdot\|_F$, $t\ge0$, expectations, $\sigma_\infty\in L^2(\mathbb R_+)$, $\min f$ → `SDEState d`, `Diffusion d m` (Euclidean norm on $d\times m$ entries = Frobenius), `ℝ≥0`, lower Lebesgue integrals in `ℝ≥0∞`, `SigmaInfL2`, `⨅ x, f x`; reason: Lean conventions; the same instances (all integrands are nonnegative, and $\min f=\inf f$ since $\mathcal S\neq\emptyset$)
--   - generalization: (3.1) and the martingale property are derived inside Theorem 3.1(i), under its hypothesis $\sigma_\infty\in L^2(\mathbb R_+)$ → no $\sigma_\infty\in L^2$ hypothesis, only (H0), (H) and $X\in S^2_d$; reason: under (H) $\sigma_\infty$ is bounded, so $\int_0^T\sigma_\infty^2<\infty$ for every $T$, which is all the bound of p.9 uses; adding $\sigma_\infty\in L^2$ gives back the page's claim
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, §3.1, proof of Theorem 3.1(i): display (3.1), p.9, and "Therefore $M_t$ is a square-integrable continuous martingale", p.10

import Definitions.Def_SDEConvexOpt_H0
import Definitions.Def_SDEConvexOpt_HypH
import Definitions.Def_SDEConvexOpt_IsFBrownian
import Definitions.Def_SDEConvexOpt_SolvesSDE
import Definitions.Def_SDEConvexOpt_InS

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

open EthierKurtz

/-- Display (3.1), p.9, and "Therefore `Mₜ` is a square-integrable continuous martingale", p.10, of
Maulen S., Fadili, Attouch, arXiv:2207.02750v1 (§3.1, proof of Theorem 3.1(i)): under (H0) and
(H), for `x⋆ ∈ S` and the anchor `φ(x) = ‖x − x⋆‖²/2`, the solution satisfies, almost surely for
all `t`,
`φ(X(t)) = ‖X₀ − x⋆‖²/2 + ½∫₀ᵗ tr Σ(s, X(s)) ds − ∫₀ᵗ ⟨∇f(X(s)), X(s) − x⋆⟩ ds + Mₜ`,
where `Mₜ = ∫₀ᵗ ⟨σ⊤(s, X(s))(X(s) − x⋆), dW(s)⟩ = ∑ₖ ∫₀ᵗ (σ⊤(s, X(s))(X(s) − x⋆))ₖ dWₖ(s)` is a
square-integrable continuous martingale.

**Formalization Note** `ℝ^d` is `SDEState d`, matrices are `Diffusion d m` (Frobenius norm), time is `ℝ≥0`, `W` is an
`𝓕`-Brownian motion (`IsFBrownian`), `X₀ ∈ ℝ^d` is deterministic, and `X` is any solution of (SDE)
(`SolvesSDE` with drift `−∇f`) in `S²_d`; by Theorem 3.1 that is the unique solution. `tr Σ(s, x) = ‖σ(s, x)‖²_F` (`Σ = σσ⊤`, p.9).
The components `Jₖ` are Itô integrals in the sense of the published
`EthierKurtz.HasBrownianItoIntegral` for the filtration `𝓕`; `M` is a Mathlib `Martingale` for
`𝓕`, in `L²` at every time, with continuous paths almost surely (the paper's "continuous", p.7). The hypothesis
`σ∞ ∈ L²(ℝ₊)` of Theorem 3.1(i), under which the page derives (3.1), is not assumed: under (H)
`σ∞` is bounded, so `∫₀ᵀ σ∞² < ∞` for every `T`, which is all the martingale claim uses. -/
theorem eq_3_1 {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsFBrownian P ℱ W) (X₀ : SDEState d)
    (f : SDEState d → ℝ) (L : ℝ≥0) (hf : H0 f L)
    (σ : ℝ≥0 × SDEState d → Diffusion d m) (hσ : HypH σ)
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : SolvesSDE P ℱ (fun p => -gradient f p.2) σ W X₀ X) (hX2 : InS 2 P X)
    (xs : SDEState d) (hxs : xs ∈ argminSet f) :
    ∃ (J : Fin m → ℝ≥0 → Ω → ℝ) (M : ℝ≥0 → Ω → ℝ),
      (∀ k, HasBrownianItoIntegral P ℱ (fun t ω => W t ω k)
        (fun s ω => ∑ i, σ (s, X s ω) (i, k) * (X s ω i - xs i)) (J k)) ∧
      (∀ t ω, M t ω = ∑ k, J k t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
      Martingale M ℱ P ∧ (∀ t, MemLp (M t) 2 P) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ‖X t ω - xs‖ ^ 2 / 2 =
        ‖X₀ - xs‖ ^ 2 / 2
          + 1 / 2 * (∫ s in (0 : ℝ)..t.val, ‖σ (s.toNNReal, X s.toNNReal ω)‖ ^ 2)
          - (∫ s in (0 : ℝ)..t.val, ⟪gradient f (X s.toNNReal ω), X s.toNNReal ω - xs⟫_ℝ)
          + M t ω := by sorry

end SDEConvexOpt
