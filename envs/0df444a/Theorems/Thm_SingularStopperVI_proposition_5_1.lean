-- Prove2me | Theorems.Thm_SingularStopperVI_proposition_5_1
-- name    : SingularStopperVI.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:55.816025+00:00
-- url     : https://prove2.me/theorems/82a99c70-cd3a-4bf4-93d4-558c8622f19e
-- title:
--   Proposition 5.1: gradient bound on $\bar{\mathcal O}_{m_0}$ independent of $q$
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The cut-offs $(\xi_m)$ of (4.1) and the penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   For each $m_0\in\mathbb N$ there is $N_1=N_1(m_0)$, independent of $\varepsilon$, $\delta$ and $q$, such that for all $q\ge m_0+2$ the solution $u$ of Problem B on $\mathcal O_q$ satisfies
--
--   $$
--   \sup_{(t,x)\in\bar{\mathcal O}_{m_0}}|\nabla u(t,x)|_d\le N_1.
--   $$
--
--   The bound on a fixed compact set no longer depends on the size of the ball on which the problem is solved.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the families $(\xi_m)$ and $(\psi_\varepsilon)$ are fixed once → $\xi$, $\psi$ are universally quantified, before the constants; reason: the constants may depend on them and not on $\varepsilon,\delta$
--   - reading: $m_0\in\mathbb N$ → every $m_0\in\mathbb N$, $0$ included; reason: the paper does not fix whether $0\in\mathbb N$; this is the stronger reading, and here $m_0$ only names the cylinder (no $g_{m_0}$ occurs)
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 5.1, (5.1), p.19

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Proposition 5.1, (5.1), p.19.
For `q ≥ m₀ + 2` the gradient of the solution of Problem B on `O_q` is bounded on `Ō_{m₀}` by
`N₁(m₀)`, independent of `ε`, `δ`, `q`. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ξ : ℕ → Euc d → ℝ} {C0 : ℝ} (hξ : IsCutoff ξ C0) {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∀ m0 : ℕ, ∃ N1 : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ q : ℕ, m0 + 2 ≤ q →
      ∀ u K, IsProblemB D Jg ξ ψ α ε δ q u K → ∀ z ∈ closedCyl d D.T m0,
        ‖K.Du z.1 z.2‖ ≤ N1 := by sorry

end SingularStopperVI
