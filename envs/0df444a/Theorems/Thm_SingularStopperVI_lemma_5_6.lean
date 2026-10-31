-- Prove2me | Theorems.Thm_SingularStopperVI_lemma_5_6
-- name    : SingularStopperVI.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:09.689987+00:00
-- url     : https://prove2.me/theorems/7d40aae7-ff5e-476d-8dae-d4d058b65215
-- title:
--   Lemma 5.6: bound on the obstacle penalty
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   With $K_2$ as in (3.10), every solution $u$ of Problem C with $\varepsilon,\delta\in(0,1)$ satisfies
--
--   $$
--   \frac1\delta\big\|(g-u)^+\big\|_\infty\le K_2.
--   $$
--
--   The bound is independent of $\varepsilon$ and $\delta$, so the obstacle $u\ge g$ survives in the limit.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - encoding: the norm $\|\cdot\|_\infty$ → the pointwise bound $\max(g-u,0)\le\delta K_2$ on $[0,T]\times\mathbb R^d$; reason: equivalent, and it avoids the junk value of a real supremum
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.6, (5.27), p.25

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.6, (5.27), p.25.
For `K₂` as in (3.10), `(1/δ)‖(g − u^{ε,δ})^+‖_∞ ≤ K₂`, stated pointwise on `[0,T] × ℝ^d`. -/
theorem lemma_5_6 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ u K, IsProblemC D ψ α ε δ u K →
      ∀ z ∈ stateDomain d D.T, max (D.g z.1 z.2 - u z.1 z.2) 0 ≤ δ * K2 := by sorry

end SingularStopperVI
