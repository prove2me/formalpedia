-- Prove2me | Theorems.Thm_SingularStopperVI_proposition_4_1
-- name    : SingularStopperVI.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:06.661741+00:00
-- url     : https://prove2.me/theorems/2754a589-e60a-4a16-8d14-22237740ab7c
-- title:
--   Proposition 4.1: a solution of Problem B is the value of the penalised game
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The cut-offs $(\xi_m)$ of (4.1) and the penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   Let $\varepsilon,\delta\in(0,1)$, $m\ge1$, and let $u$ be a solution of Problem B on $\mathcal O_m$. For all $(t,x)\in\bar{\mathcal O}_m$,
--
--   $$
--   u(t,x)=\inf_{(n,\nu)\in\mathcal A^\circ_t}\ \sup_{w\in\mathcal T^\delta_t}\mathcal J^{\varepsilon,\delta,m}_{t,x}(n,\nu,w)=\sup_{w\in\mathcal T^\delta_t}\ \inf_{(n,\nu)\in\mathcal A^\circ_t}\mathcal J^{\varepsilon,\delta,m}_{t,x}(n,\nu,w).
--   $$
--
--   This identifies the penalised PDE on a ball with a zero-sum game of control in which the stopper is replaced by a bounded killing intensity $w$.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - reading: "$|n_s|_d=1$, P-a.s. for all $s$" → almost surely, for all $s$ (`∀ᵐ ω, ∀ s`); reason: at fixed times alone, $|n|\neq 1$ at a random jump time would be allowed, and displacement would no longer match the cost
--   - encoding: the families $(\xi_m)$ and $(\psi_\varepsilon)$ are fixed once → $\xi$, $\psi$ are universally quantified, before the constants; reason: the constants may depend on them and not on $\varepsilon,\delta$
--   - encoding: $m\in\mathbb N$ → $1\le m$; reason: $g_m$ uses $\xi_{m-1}$
--   - encoding: $(n,\nu)\in\mathcal A^\circ_t$ with $\nu$ absolutely continuous → $(n,\dot\nu)$, with $\dot\nu$ progressive, non-negative and locally integrable, and infima over triples with the state $X$; reason: only $\dot\nu$ enters the dynamics and the payoffs, and an adapted absolutely continuous $\nu$ has a progressive density
--   - encoding: real Hamiltonians, real payoffs → values in $[0,\infty]$; the supremum of the real expression is taken after truncation at $0$; reason: the real supremum is non-negative (take $p=0$) and all integrands are non-negative
--   - encoding: $u=$ value → $0\le u$ and `ENNReal.ofReal u =` value; reason: the values live in $[0,\infty]$; non-negativity is part of the identity, and it makes `ofReal` lossless
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 4.1, (4.8), p.9

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 4.1, (4.8), p.9.
A solution of Problem B is the common value of the penalised game on `O_m`. The clause `0 ≤ u` is
needed to read the real `u` in `[0,∞]`; it is part of (4.8), whose values are non-negative. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ξ : ℕ → Euc d → ℝ} {C0 : ℝ} (hξ : IsCutoff ξ C0) {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ m : ℕ, 1 ≤ m → ∀ u K,
      IsProblemB D Jg ξ ψ α ε δ m u K → ∀ z ∈ closedCyl d D.T m,
        0 ≤ u z.1 z.2 ∧
        ENNReal.ofReal (u z.1 z.2) = upperValueM B D Jg ξ ψ ε δ m z.1 z.2 ∧
        ENNReal.ofReal (u z.1 z.2) = lowerValueM B D Jg ξ ψ ε δ m z.1 z.2 := by sorry

end SingularStopperVI
