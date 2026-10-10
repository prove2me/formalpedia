-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_theorem_3_13
-- name    : SmoothCCP.Feasibility.theorem_3_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:27.557639+00:00
-- url     : https://prove2.me/theorems/6c1172c8-f95f-4c47-8136-2b2ba126ca20
-- title:
--   Theorem 3.13 — ℙ(X^{N,2t}_{ε,(δ−β)} ⊆ X_α) ≥ 1 − ⌈1/β⌉⌈2LD/t⌉ⁿ exp{−2NM²} for bounded X and C Lipschitz in x
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed, $\alpha\in(0,1)$, and let $\Gamma_\varepsilon$ be built from an admissible $\gamma_\varepsilon$. Let $\xi_1,\dots,\xi_N$ ($N\ge1$) be an i.i.d. sample with the law $\mathbb P_\xi$ of $\xi$, and assume that $C(x,\xi)$ has a continuous distribution for each $x\in X$ (Assumption 3.1). Suppose:
--
--   1. $X$ is bounded with diameter $D>0$: $\|x-y\|_\infty\le D$ for all $x,y\in X$;
--   2. (Assumption 3.12) there is $L>0$ with $|C(x,\xi)-C(y,\xi)|\le L\|x-y\|_\infty$ for all $x,y\in X$, with probability one;
--   3. (Assumption 3.7) $t>0$, $\delta\in(0,\alpha]$, and $M:=\inf_{x\in X}\bigl(F(0;x)-F_\varepsilon(-t;x)+(\alpha-\delta)\bigr)>0$.
--
--   Then for every $\beta\in(0,\delta]$,
--   $$\mathbb P\bigl(X^{N,2t}_{\varepsilon,(\delta-\beta)}\subseteq X_\alpha\bigr)\ge 1-\lceil1/\beta\rceil\,\lceil 2LD/t\rceil^n\exp\{-2NM^2\}.$$
--
--   The theorem gives an explicit sample size under which every point accepted by the smoothed sample approximation, with shift $2t$ and risk level $\delta-\beta$, is feasible for the original chance-constrained problem with high probability, uniformly over a bounded, possibly infinite decision set.
--
--   **Formalization Note** The conclusion is stated in the complement form $\mathbb P(X^{N,2t}_{\varepsilon,(\delta-\beta)}\not\subseteq X_\alpha)\le\lceil1/\beta\rceil\lceil2LD/t\rceil^n e^{-2NM^2}$ with $\mathbb P$ evaluated as an outer measure, because the event quantifies over uncountably many $x$ and need not be measurable; this form implies the printed one. The norm is the sup norm of `Fin n → ℝ`. $D$ is an upper bound on the sup-norm diameter and is required positive: at $D=0$ (one point) and $n\ge1$ the printed bound reads "$\ge1$", which fails when the point is infeasible; the bound increases in $D$, so for a set of positive diameter the two readings agree, and the sup-norm diameter never exceeds the Euclidean one. $M$ is a positive lower bound of $M_x$ on $X$, equivalent to the infimum since the bound decreases in $M$. Added relative to the page: $C(x,\cdot)$ measurable for $x\in X$, and $N\ge1$. "With probability one" in Assumption 3.12 is over $\xi\sim\mathbb P_\xi$, with the quantifier over $x,y$ inside.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Theorem 3.13, p. 14 (Assumption 3.12, p. 14; Assumption 3.7, p. 11; Assumption 3.1, p. 9)

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem theorem_3_13 {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (D : ℝ) (hD : 0 < D) (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ᵐ s ∂Pξ, ∀ x ∈ X, ∀ y ∈ X, |C x s - C y s| ≤ L * ‖x - y‖)
    (t δ M : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (hδα : δ ≤ α) (hM : 0 < M)
    (hMx : ∀ x ∈ X, M ≤ margin Pξ C ε γ t α δ x)
    (β : ℝ) (hβ0 : 0 < β) (hβδ : β ≤ δ) :
    P {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) (2 * t) (δ - β) ⊆ trueFeasible Pξ C X α}
      ≤ ENNReal.ofReal
          ((⌈1 / β⌉₊ : ℝ) * (⌈2 * L * D / t⌉₊ : ℝ) ^ n * Real.exp (-2 * (N : ℝ) * M ^ 2)) := by sorry

end SmoothCCP.Feasibility
