-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_theorem_3_8
-- name    : SmoothCCP.Feasibility.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:15.301113+00:00
-- url     : https://prove2.me/theorems/5b3f31e1-517a-411a-9cf1-0d162ff23200
-- title:
--   Theorem 3.8 — for x ∈ X \ X_α under Assumption 3.7, ℙ(F^N_ε(−t; x) ≥ 1 − δ) ≤ exp{−2NM_x²}
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed, $\alpha\in(0,1)$, and let $\Gamma_\varepsilon$ be built from an admissible $\gamma_\varepsilon$. Let $\xi_1,\dots,\xi_N$ ($N\ge1$) be an i.i.d. sample with the law $\mathbb P_\xi$ of $\xi$. Assume that for each $x\in X$ the random variable $C(x,\xi)$ has a continuous distribution (Assumption 3.1).
--
--   Suppose Assumption 3.7 holds: $t\in\mathbb R$, $\delta\in[0,\alpha]$, and $M:=\inf_{x\in X}M_x>0$, where $M_x=F(0;x)-F_\varepsilon(-t;x)+(\alpha-\delta)$. Let $x\in X$ with $x\notin X_\alpha$. Then
--   $$\mathbb P\bigl(F^N_\varepsilon(-t;x)\ge 1-\delta\bigr)\le \exp\{-2NM_x^2\}.$$
--
--   This is the per-point probabilistic feasibility guarantee: an infeasible point passes the shifted, tightened sample test only with probability exponentially small in the sample size. Theorem 3.11 sums it over a finite feasible region.
--
--   **Formalization Note** Assumption 3.7's infimum is encoded by a number $M>0$ with $M\le M_x$ for all $x\in X$, which is equivalent and avoids a junk real infimum. The paper's standing hypotheses are included: $X$ closed (p. 1), Assumption 3.1 (as $\mathbb P_\xi(C(x,\xi)=y)=0$ for every $y$) and $0<\alpha<1$. Added: $C(x,\cdot)$ is measurable for $x\in X$ ("$C(x,\xi)$ is a random variable"), and $N\ge 1$. The sample is a family $\xi_i:\Omega\to\Xi$ of measurable, mutually independent maps on a probability space, each with law $\mathbb P_\xi$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Theorem 3.8, p. 12 (Assumption 3.7, p. 11; Assumption 3.1, p. 9)

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem theorem_3_8 {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (t δ M : ℝ) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) (hM : 0 < M)
    (hMx : ∀ x ∈ X, M ≤ margin Pξ C ε γ t α δ x)
    (x : Fin n → ℝ) (hxX : x ∈ X) (hx : x ∉ trueFeasible Pξ C X α) :
    P {ω | 1 - δ ≤ sampleCdf C ε γ (fun i => ξ i ω) (-t) x}
      ≤ ENNReal.ofReal (Real.exp (-2 * (N : ℝ) * (margin Pξ C ε γ t α δ x) ^ 2)) := by sorry

end SmoothCCP.Feasibility
