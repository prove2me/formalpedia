-- Prove2me | Theorems.Thm_SingularStopperVI_theorem_6_1
-- name    : SingularStopperVI.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:55.313807+00:00
-- url     : https://prove2.me/theorems/86c69cfc-bb82-42a3-a9e8-1f7db5e48474
-- title:
--   Theorem 6.1: existence for Problem A
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3.
--
--   For every $p>d+2$ there is a solution $u$ of Problem A: $u\in W^{1,2,p}_{\ell oc}(\mathbb R^{d+1}_{0,T})$ of quadratic growth solving the variational inequality (3.5) with obstacle $g$ and gradient constraint $f$.
--
--   This is the first half of the proof of the goal theorem.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - reading: "for all $(t,x)\in\mathcal C\cap\mathcal I$" in (3.5) for a $W^{1,2,p}$ function → on $\mathcal C\cap\mathcal I$, $u$ is classically $C^{1,2}$ and the equation holds at every point for the classical derivatives; reason: a Sobolev function has no pointwise derivatives; the proof of Theorem 6.1 (p.31) obtains this by standard PDE theory
--   - reading: $u\ge g$ and $|\nabla u|_d\le f$ "for all $(t,x)$" in (3.5) → $u$ and the gradient are the continuous representatives on $[0,T]\times\mathbb R^d$; reason: so the page says below Problem A, by (2.2)
--   - reading: Problem A fixes $p>d+2$ → the statement holds for every $p>d+2$; reason: the strongest reading of "Fix $p$"
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 6.1, p.30

import Mathlib
import Definitions.Def_SingularStopperVI_Assumptions

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 6.1, p.30.
For every `p > d + 2`, Problem A has a solution. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2) :
    ∀ p : ℝ, (d : ℝ) + 2 < p → ∃ u, IsProblemASolution D p u := by sorry

end SingularStopperVI
