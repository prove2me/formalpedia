-- Prove2me | Theorems.Thm_SingularStopperVI_lemma_5_8
-- name    : SingularStopperVI.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:36.844799+00:00
-- url     : https://prove2.me/theorems/781a130b-d3bb-4252-8553-72347a827205
-- title:
--   Lemma 5.8: bound on the gradient penalty on $\bar{\mathcal O}_m$
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   For each $m\in\mathbb N$ there is $M_5=M_5(m)$, independent of $\varepsilon$ and $\delta$, such that every solution $u$ of Problem C satisfies
--
--   $$
--   \big\|\psi_\varepsilon(|\nabla u|_d^2-f^2)\big\|_{C^0(\bar{\mathcal O}_m)}\le M_5.
--   $$
--
--   The bound is what keeps the gradient constraint $|\nabla u|_d\le f$ in the limit.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - encoding: $\nabla u$ of a solution of Problem C at $t=T$ → the gradient witness `K.Du`, continuous on $[0,T]\times\mathbb R^d$; reason: $C^{1,2,\alpha}_{Loc}$ gives no gradient at $T$; the embedding (2.2) gives this continuous representative
--   - reading: $m\in\mathbb N$ → every $m\in\mathbb N$, $0$ included; reason: the paper does not fix whether $0\in\mathbb N$; this is the stronger reading, and here $m$ only names the cylinder (no $g_{m}$ occurs)
--   - encoding: the norm $\|\cdot\|_{C^0(\bar{\mathcal O}_m)}$ → the pointwise bound at every point of $\bar{\mathcal O}_m$; reason: equivalent
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.8, (5.31), p.26

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 5.8, (5.31), p.26.
`‖ψ_ε(|∇u^{ε,δ}|_d² − f²)‖_{C⁰(Ō_m)} ≤ M₅(m)`, with `M₅` independent of `ε`, `δ`, pointwise on `Ō_m`. -/
theorem lemma_5_8 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ m : ℕ, ∃ M5 : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ u K,
      IsProblemC D ψ α ε δ u K → ∀ z ∈ closedCyl d D.T m,
        |ψ ε (‖K.Du z.1 z.2‖ ^ 2 - D.f z.1 z.2 ^ 2)| ≤ M5 := by sorry

end SingularStopperVI
