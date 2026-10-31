-- Prove2me | Theorems.Thm_SingularStopperVI_theorem_3_3
-- name    : SingularStopperVI.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:06.302037+00:00
-- url     : https://prove2.me/theorems/eaf76353-a3fa-443b-b7db-b8000b1a7c2b
-- title:
--   Theorem 3.3: the value of the game is the maximal solution of Problem A, and $\tau_*$ is optimal
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3.
--
--   The game of (3.3) has a value: for all $(t,x)\in[0,T]\times\mathbb R^d$,
--
--   $$
--   \underline v(t,x)=\sup_{\tau\in\mathcal T_t}\inf_{(n,\nu)\in\mathcal A_t}J_{t,x}(n,\nu,\tau)=\inf_{(n,\nu)\in\mathcal A_t}\sup_{\tau\in\mathcal T_t}J_{t,x}(n,\nu,\tau)=\overline v(t,x)<\infty .
--   $$
--
--   Let $v$ be this value. For every $p>d+2$:
--
--   1. $v$ solves Problem A;
--   2. every solution $u$ of Problem A satisfies $u\le v$ on $[0,T]\times\mathbb R^d$.
--
--   Moreover, for any $(t,x)$ and any $(n,\nu)\in\mathcal A_t$ with state $X$, the time
--
--   $$
--   \tau_*=\inf\{s\ge0\mid v(t+s,X_s)=g(t+s,X_s)\}\wedge(T-t)
--   $$
--
--   belongs to $\mathcal T_t$, and it is optimal for the stopper:
--
--   $$
--   v(t,x)=\inf_{(n,\nu)\in\mathcal A_t}J_{t,x}(n,\nu,\tau_*(n,\nu)).
--   $$
--
--   In particular $v(t,x)\le J_{t,x}(n,\nu,\tau_*(n,\nu))$ for each control, so $\tau_*$ is a best response to every control. The result needs no boundedness of the coefficients or of the payoffs, and no uniform ellipticity.
--
--   Differences from the source:
--   - encoding: real expectations $J$ and values → values in $[0,\infty]$ (`lintegral`); reason: the payoff can be $+\infty$, since $f$ has polynomial growth and $\nu$ a second moment only, and all integrands are non-negative
--   - encoding: infima over $(n,\nu)\in\mathcal A_t$ → infima over triples $(n,\nu,X)$ with $X$ a solution of (3.1); reason: (3.1) is well posed, by the claim after (3.1)
--   - encoding: $d\nu^c$, the continuous part of $\nu$ → $d\nu$ restricted to the times without a jump; reason: these are the same measure
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - encoding: $v$, a real number → `valueFn`, the `toReal` of the lower value; reason: the first clause proves that it is finite
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: $\inf\{s\ge0\mid\dots\}\wedge(T-t)$ over all $s\ge0$ → the infimum over $s\in[0,T-t]$ with $T-t$ in the set; reason: times after $T-t$ lie off the domain of $v$, $g$, and the minimum makes them irrelevant; no $\inf\emptyset$ occurs
--   - reading: "$|n_s|_d=1$, P-a.s. for all $s$" → almost surely, for all $s$ (`∀ᵐ ω, ∀ s`); reason: at fixed times alone, $|n|\neq 1$ at a random jump time would be allowed, and displacement would no longer match the cost
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - reading: "for all $(t,x)\in\mathcal C\cap\mathcal I$" in (3.5) for a $W^{1,2,p}$ function → on $\mathcal C\cap\mathcal I$, $u$ is classically $C^{1,2}$ and the equation holds at every point for the classical derivatives; reason: a Sobolev function has no pointwise derivatives; the proof of Theorem 6.1 (p.31) obtains this by standard PDE theory
--   - reading: $u\ge g$ and $|\nabla u|_d\le f$ "for all $(t,x)$" in (3.5) → $u$ and the gradient are the continuous representatives on $[0,T]\times\mathbb R^d$; reason: so the page says below Problem A, by (2.2)
--   - reading: Problem A fixes $p>d+2$ → the statement holds for every $p>d+2$; reason: the strongest reading of "Fix $p$"
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 3.3, p.7

import Mathlib
import Definitions.Def_SingularStopperVI_Assumptions

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 3.3, p.7 (repeated as Theorem 6.2, p.31).
The game has a value (3.4), which is finite. For every `p > d + 2`, the value function `v` solves
Problem A and dominates every solution of Problem A. For every `(t,x)` and every admissible control
with its state, `τ_*` of (3.11) lies in `𝒯_t`, and it is optimal for the stopper:
`v(t,x) = inf_{(n,ν) ∈ 𝒜_t} J_{t,x}(n,ν,τ_*(n,ν))`.

**Formalization Note** `valueFn` is the real part of `lowerValue`, which the first clause shows to
be finite. `τ_*` is a function of the state, built from `valueFn`. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2) :
    (∀ t ∈ Icc 0 D.T, ∀ x, lowerValue B D t x = upperValue B D t x ∧ lowerValue B D t x ≠ ⊤) ∧
    (∀ p : ℝ, (d : ℝ) + 2 < p → IsProblemASolution D p (valueFn B D)) ∧
    (∀ p : ℝ, (d : ℝ) + 2 < p → ∀ w, IsProblemASolution D p w →
      ∀ t ∈ Icc 0 D.T, ∀ x, w t x ≤ valueFn B D t x) ∧
    ∀ t ∈ Icc 0 D.T, ∀ x,
      (∀ c : ControlledState B D t x,
        IsStoppingRule B (horizon D t) (tauStar D (valueFn B D) t c.1.2.2)) ∧
      lowerValue B D t x =
        ⨅ c : ControlledState B D t x, c.payoff (tauStar D (valueFn B D) t c.1.2.2) := by sorry

end SingularStopperVI
