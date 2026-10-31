-- Prove2me | Theorems.Thm_SingularStopperVI_lemma_4_5
-- name    : SingularStopperVI.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:36.893003+00:00
-- url     : https://prove2.me/theorems/04e0e525-ab41-4eea-8040-4722d7ee1265
-- title:
--   Lemma 4.5: quadratic growth of solutions of Problem B, uniform in the penalisation
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The cut-offs $(\xi_m)$ of (4.1) and the penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   There is $K_3>0$, independent of $\varepsilon$, $\delta$ and $m$, such that every solution $u$ of Problem B on $\mathcal O_m$, $\varepsilon,\delta\in(0,1)$, satisfies
--
--   $$
--   0\le u(t,x)\le K_3(1+|x|_d^2),\qquad (t,x)\in\bar{\mathcal O}_m.
--   $$
--
--   This is the growth estimate that passes to every later limit.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the families $(\xi_m)$ and $(\psi_\varepsilon)$ are fixed once → $\xi$, $\psi$ are universally quantified, before the constants; reason: the constants may depend on them and not on $\varepsilon,\delta$
--   - encoding: $m\in\mathbb N$ → $1\le m$; reason: $g_m$ uses $\xi_{m-1}$
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 4.5, (4.18), p.11

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Lemma 4.5, (4.18), p.11.
Solutions of Problem B have quadratic growth, with a constant `K₃` independent of `ε`, `δ`, `m`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ξ : ℕ → Euc d → ℝ} {C0 : ℝ} (hξ : IsCutoff ξ C0) {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∃ K3 : ℝ, 0 < K3 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ m : ℕ, 1 ≤ m → ∀ u K,
      IsProblemB D Jg ξ ψ α ε δ m u K → ∀ z ∈ closedCyl d D.T m,
        0 ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ K3 * (1 + ‖z.2‖ ^ 2) := by sorry

end SingularStopperVI
