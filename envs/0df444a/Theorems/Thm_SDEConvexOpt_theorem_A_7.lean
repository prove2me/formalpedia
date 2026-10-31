-- Prove2me | Theorems.Thm_SDEConvexOpt_theorem_A_7
-- name    : SDEConvexOpt.theorem_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:37.181822+00:00
-- url     : https://prove2.me/theorems/1f81d3f9-6f2c-4109-877e-cd3ea2ff6082
-- title:
--   Theorem A.7 (corrected: $F(\cdot,0)$, $G(\cdot,0)$ bounded on $[0,T]$) — strong existence in every $S^l_d$, $l\ge2$, and uniqueness for Lipschitz SDEs
-- statement:
--   Let $F:\mathbb R_+\times\mathbb R^d\to\mathbb R^d$ and $G:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ be measurable and assume that for every $T>0$ there are constants $C_1\ge0$ and $C$ with
--   $$
--   \|F(t,x)-F(t,y)\|+\|G(t,x)-G(t,y)\|_F\le C_1\|x-y\|,\qquad \|F(t,0)\|+\|G(t,0)\|_F\le C,
--   $$
--   for all $x,y\in\mathbb R^d$ and $t\in[0,T]$. Let $W$ be an $m$-dimensional Brownian motion with respect to $(\mathcal F_t)$ and $X_0\in\mathbb R^d$. Consider
--   $$
--   dX(t)=F(t,X(t))\,dt+G(t,X(t))\,dW(t),\qquad X(0)=X_0. \tag{A.1}
--   $$
--
--   1. If $\mathcal F_0$ contains the $\mathbb P$-null events, (A.1) has a solution $X$ with $\mathbb E\sup_{t\le T}\|X(t)\|^l<\infty$ for every $T\ge0$ and every real $l\ge2$.
--   2. Any two solutions of (A.1) in $S^2_d$ are indistinguishable: almost surely $X(t)=Y(t)$ for all $t\ge0$.
--
--   This is the well-posedness result that gives the first sentence of Theorem 3.1, with $F=-\nabla f$ and $G=\sigma$.
--
--   Differences from the source:
--   - correction: (A.2) alone, a bound on differences only → added: for every $T>0$, $\sup_{t\in[0,T]}(\|F(t,0)\|+\|G(t,0)\|_F)<\infty$; reason: as printed the theorem is false: $d=m=1$, $F(t,x)=1/t$ for $t>0$, $F(0,x)=0$, $G=0$ are measurable and satisfy (A.2) with $C_1=0$, yet $X(t)=X_0+\int_0^t ds/s$ diverges, so no solution exists; the proof's first line (linear growth with $C_2$) needs exactly the added bound
--   - reading: "for every $T>0$: (A.2) … for some constant $C_1\ge0$" → $C_1$ (and the added $C$) may depend on $T$; reason: the quantifier order of the page; it is the weaker hypothesis, so the stronger theorem
--   - reading: "W is a $\mathcal F_t$-adapted m-dimensional Brownian Motion" (A.1), p.34 → `IsFBrownian`: a standard m-dimensional Brownian motion, adapted to $\mathcal F$, with $W(t)-W(s)$ independent of $\mathcal F_s$ for $s\le t$; reason: the standard meaning of a Brownian motion with respect to a filtration; with adaptedness alone the stochastic integrals of p.10 need not be martingales and the cited existence theorems do not apply
--   - reading: initial condition $X_0$ of (A.1) → a deterministic $X_0\in\mathbb R^d$; reason: (A.1) is used only for (SDE), whose initial condition is $X_0\in\mathbb R^d$ (p.2)
--   - reading: no condition on the filtered probability space (p.7) → existence assumes `F0Complete`: $\mathcal F_0$ contains the $\mathbb P$-null events; reason: the cited theorems [33, Thm 5.2.1], [35, Thm 2.4.1] work under the usual conditions; without completeness an adapted modification of the Picard limit with continuous paths need not exist; uniqueness is stated without it
--   - reading: "has a unique solution $X\in S^l_d$, for every $l\ge2$" → a solution exists and lies in $S^l_d$ for every real $l\ge2$; any two solutions in $S^2_d$ are indistinguishable; reason: $S^l_d\subset S^2_d$ for $l\ge2$, so uniqueness in $S^2_d$ is the strongest literal reading; $S^l_d$ is a quotient by indistinguishability (p.7)
--   - encoding: solutions are progressively measurable processes with almost surely continuous paths, taken modulo indistinguishability (the relation $\mathcal R$ and $S^0_d$, p.7) → `SolvesSDE`: adapted processes with every path continuous, the integral equation outside one null set; reason: adapted plus continuous gives progressive measurability; when $\mathcal F_0$ contains the null sets every class of $S^0_d$ has such a representative, and every conclusion is invariant under indistinguishability
--   - encoding: $\mathbb R^d$, $\mathbb R^{d\times m}$ with $\|\cdot\|_F$, $t\ge0$, expectations, $\sigma_\infty\in L^2(\mathbb R_+)$, $\min f$ → `SDEState d`, `Diffusion d m` (Euclidean norm on $d\times m$ entries = Frobenius), `ℝ≥0`, lower Lebesgue integrals in `ℝ≥0∞`, `SigmaInfL2`, `⨅ x, f x`; reason: Lean conventions; the same instances (all integrands are nonnegative, and $\min f=\inf f$ since $\mathcal S\neq\emptyset$)
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem A.7 and (A.1)–(A.2), p.34

import Definitions.Def_SDEConvexOpt_F0Complete
import Definitions.Def_SDEConvexOpt_IsFBrownian
import Definitions.Def_SDEConvexOpt_SolvesSDE
import Definitions.Def_SDEConvexOpt_InS

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

open EthierKurtz

/-- Theorem A.7 (corrected) of Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex
optimization, arXiv:2207.02750v1, p.34 (after Øksendal [33, Theorem 5.2.1] and Mao
[35, Theorem 2.4.1]): let `F : ℝ₊ × ℝ^d → ℝ^d` and `G : ℝ₊ × ℝ^d → ℝ^{d×m}` be measurable and
satisfy, for every `T > 0`, (A.2):
`‖F(t, x) − F(t, y)‖ + ‖G(t, x) − G(t, y)‖_F ≤ C₁ ‖x − y‖` for all `x, y` and `t ∈ [0, T]`, for
some `C₁ ≥ 0`. Then (A.1) `dX = F(t, X) dt + G(t, X) dW`, `X(0) = X₀`, has a unique solution
`X ∈ S^l_d`, for every `l ≥ 2`.

**Formalization Note** Corrected: the hypothesis `sup_{t ∈ [0, T]} (‖F(t, 0)‖ + ‖G(t, 0)‖_F) < ∞`
for every `T > 0` is added. As printed the theorem is false: `d = m = 1`, `F(t, x) = 1/t`
(`F(0, x) = 0`), `G = 0` satisfy (A.2) with `C₁ = 0`, and no solution exists. `C₁` may depend on
`T`. `W` is an `𝓕`-Brownian motion (`IsFBrownian`); `X₀ ∈ ℝ^d` is deterministic. Existence
assumes that `𝓕₀` contains the `ℙ`-null sets (`F0Complete`); uniqueness is up to
indistinguishability among solutions in `S²_d`. -/
theorem theorem_A_7 {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsFBrownian P ℱ W) (X₀ : SDEState d)
    (F : ℝ≥0 × SDEState d → SDEState d) (G : ℝ≥0 × SDEState d → Diffusion d m)
    (hFm : Measurable F) (hGm : Measurable G)
    (hLip : ∀ T : ℝ≥0, 0 < T → ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (x y : SDEState d) (t : ℝ≥0), t ≤ T →
      ‖F (t, x) - F (t, y)‖ + ‖G (t, x) - G (t, y)‖ ≤ C₁ * ‖x - y‖)
    (hZero : ∀ T : ℝ≥0, 0 < T → ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ T → ‖F (t, 0)‖ + ‖G (t, 0)‖ ≤ C) :
    (F0Complete P ℱ →
      ∃ X : ℝ≥0 → Ω → SDEState d, SolvesSDE P ℱ F G W X₀ X ∧ ∀ l : ℝ, 2 ≤ l → InS l P X) ∧
    ∀ X Y : ℝ≥0 → Ω → SDEState d,
      SolvesSDE P ℱ F G W X₀ X → InS 2 P X → SolvesSDE P ℱ F G W X₀ Y → InS 2 P Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by sorry

end SDEConvexOpt
