-- Prove2me | Theorems.Thm_SingularStopperVI_proposition_5_4
-- name    : SingularStopperVI.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:18.965037+00:00
-- url     : https://prove2.me/theorems/eb369eef-9b99-419c-b920-b8fdd587931e
-- title:
--   Proposition 5.4: a solution of Problem C is the value of the penalised game
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   Let $\varepsilon,\delta\in(0,1)$ and let $u$ be a solution of Problem C. For all $(t,x)\in[0,T]\times\mathbb R^d$,
--
--   $$
--   u(t,x)=\inf_{(n,\nu)\in\mathcal A^\circ_t}\ \sup_{w\in\mathcal T^\delta_t}\mathcal J^{\varepsilon,\delta}_{t,x}(n,\nu,w)=\sup_{w\in\mathcal T^\delta_t}\ \inf_{(n,\nu)\in\mathcal A^\circ_t}\mathcal J^{\varepsilon,\delta}_{t,x}(n,\nu,w).
--   $$
--
--   In particular, two solutions of Problem C agree on $[0,T]\times\mathbb R^d$.
--
--   The statement is for every solution of Problem C, as printed; Problem C carries no growth condition.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - reading: "$|n_s|_d=1$, P-a.s. for all $s$" → almost surely, for all $s$ (`∀ᵐ ω, ∀ s`); reason: at fixed times alone, $|n|\neq 1$ at a random jump time would be allowed, and displacement would no longer match the cost
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - encoding: $\nabla u$ of a solution of Problem C at $t=T$ → the gradient witness `K.Du`, continuous on $[0,T]\times\mathbb R^d$; reason: $C^{1,2,\alpha}_{Loc}$ gives no gradient at $T$; the embedding (2.2) gives this continuous representative
--   - encoding: $(n,\nu)\in\mathcal A^\circ_t$ with $\nu$ absolutely continuous → $(n,\dot\nu)$, with $\dot\nu$ progressive, non-negative and locally integrable, and infima over triples with the state $X$; reason: only $\dot\nu$ enters the dynamics and the payoffs, and an adapted absolutely continuous $\nu$ has a progressive density
--   - encoding: real Hamiltonians, real payoffs → values in $[0,\infty]$; the supremum of the real expression is taken after truncation at $0$; reason: the real supremum is non-negative (take $p=0$) and all integrands are non-negative
--   - encoding: $u=$ value → $0\le u$ and `ENNReal.ofReal u =` value; reason: the values live in $[0,\infty]$; non-negativity is part of the identity, and it makes `ofReal` lossless
--   - generalization: Proposition 5.4 is the identity (5.19) → also the uniqueness of the solution of Problem C; reason: stated on p.25 as a consequence of (5.19); dropping the clause gives the printed statement
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 5.4, (5.19), p.23, and the consequence stated on p.25

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 5.4, (5.19), p.23, with the consequence stated on p.25.
A solution of Problem C is the common value of the penalised game on `[0,T] × ℝ^d`, and Problem C has
at most one solution. The clause `0 ≤ u` is needed to read the real `u` in `[0,∞]`. -/
theorem proposition_5_4 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ u K, IsProblemC D ψ α ε δ u K →
      (∀ z ∈ stateDomain d D.T,
        0 ≤ u z.1 z.2 ∧
        ENNReal.ofReal (u z.1 z.2) = upperValueC B D ψ ε δ z.1 z.2 ∧
        ENNReal.ofReal (u z.1 z.2) = lowerValueC B D ψ ε δ z.1 z.2) ∧
      ∀ u' K', IsProblemC D ψ α ε δ u' K' → ∀ z ∈ stateDomain d D.T,
        u z.1 z.2 = u' z.1 z.2 := by sorry

end SingularStopperVI
