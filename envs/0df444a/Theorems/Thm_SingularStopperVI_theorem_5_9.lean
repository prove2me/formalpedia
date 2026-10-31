-- Prove2me | Theorems.Thm_SingularStopperVI_theorem_5_9
-- name    : SingularStopperVI.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:07.137466+00:00
-- url     : https://prove2.me/theorems/8a913444-6953-480c-9aae-edc187e9b906
-- title:
--   Theorem 5.9: Sobolev bound independent of $\varepsilon$, $\delta$
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   For every $p\in(1,\infty)$ and $m\in\mathbb N$ there is $M_6=M_6(m,p)$ such that every solution $u$ of Problem C satisfies
--
--   $$
--   \|u\|_{W^{1,2,p}(\mathcal O_m)}\le M_6\qquad\text{for all }\varepsilon,\delta\in(0,1).
--   $$
--
--   This is the compactness that gives a limit as $\varepsilon,\delta\to0$.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - reading: $m\in\mathbb N$ → every $m\in\mathbb N$, $0$ included; reason: the paper does not fix whether $0\in\mathbb N$; this is the stronger reading, and here $m$ only names the cylinder (no $g_{m}$ occurs)
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 5.9, (5.40), p.30

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 5.9, (5.40), p.30.
For `p ∈ (1,∞)`, `‖u^{ε,δ}‖_{W^{1,2,p}(O_m)} ≤ M₆(m,p)` for all `ε, δ ∈ (0,1)`. -/
theorem theorem_5_9 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ m : ℕ, ∀ p : ℝ, 1 < p → ∃ M6 : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ u K,
      IsProblemC D ψ α ε δ u K → w12pNorm p (openCyl d D.T m) u K ≤ ENNReal.ofReal M6 := by sorry

end SingularStopperVI
