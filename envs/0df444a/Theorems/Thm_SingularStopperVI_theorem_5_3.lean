-- Prove2me | Theorems.Thm_SingularStopperVI_theorem_5_3
-- name    : SingularStopperVI.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:45.012012+00:00
-- url     : https://prove2.me/theorems/15dd0ba5-34a4-4859-93ac-92e086e325eb
-- title:
--   Theorem 5.3: existence for Problem C, with quadratic growth
-- statement:
--   Throughout, $b,\sigma$ satisfy Assumption 3.1, $f,g,h$ satisfy Assumption 3.2, $T>0$, $r\ge0$, and $(\Omega,\mathcal F,\mathbb F,\mathsf P,W)$ is the stochastic basis of §3. The penalties $(\psi_\varepsilon)$ of p.8 are fixed.
--
--   There is $K_3>0$ such that for all $\varepsilon,\delta\in(0,1)$ Problem C has a solution $u$ with
--
--   $$
--   0\le u(t,x)\le K_3(1+|x|_d^2),\qquad (t,x)\in[0,T]\times\mathbb R^d.
--   $$
--
--   Problem C is the penalised problem on the whole of $[0,T]\times\mathbb R^d$, and its solutions are the functions from which the solution of Problem A is obtained.
--
--   Differences from the source:
--   - encoding: the stochastic basis is fixed at the start of §3 → a universally quantified basis `B` with `B.IsValid`, also where the conclusion does not mention it; reason: it is the paper's standing setting, and the proof is probabilistic
--   - encoding: "for some $\alpha$", "there is $K_0$, $K_1$, $K_2$" in Assumption 3.2, and the derivatives of $g$ → $\alpha$, $K_0$, $K_1$, $K_2$ and $J_g$ are parameters of `Assumption32`; reason: universally quantifying over the data of a hypothesis is the same as assuming that they exist; Lemmas 5.6 and 5.7 name these constants
--   - encoding: bounded sets $\mathcal O\subset\mathbb R^{d+1}_{0,T}$ and $B\subset\mathbb R^d$ → the cylinders $[0,T]\times\bar B_R$ and the balls $\bar B_R$; reason: they exhaust the bounded sets, and the classes are monotone in the set
--   - reading: "$\mathbb F$-adapted Brownian motion" (p.5) → an $\mathbb F$-Brownian motion: increments after $s$ are independent of $\mathcal F_s$; reason: the Itô integral in (3.1) is not defined otherwise
--   - reading: (3.7) prints "all $x\in\mathbb R^{d+1}_{0,T}$" → $x\in\mathbb R^d$; reason: $h(t,x)$ and $g(t,x)$ take $x\in\mathbb R^d$; a slip of the page
--   - encoding: the family $(\psi_\varepsilon)$ is fixed once → $\psi$ is universally quantified, before the constants; reason: the constants may depend on it and not on $\varepsilon,\delta$
--   - encoding: $\nabla u$ of a solution of Problem C at $t=T$ → the gradient witness `K.Du`, continuous on $[0,T]\times\mathbb R^d$; reason: $C^{1,2,\alpha}_{Loc}$ gives no gradient at $T$; the embedding (2.2) gives this continuous representative
--   - generalization: "There exists a solution of Problem C" → a solution that also satisfies $0\le u\le K_3(1+|x|_d^2)$ with one $K_3$; reason: the constructed solution is a locally uniform limit of solutions of Problem B, so (4.18) passes to it; the proof of Theorem 6.2 uses this; dropping the clause gives the printed statement
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 5.3, p.22; bound (4.18), used at the end of the proof of Theorem 6.1, p.31

import Mathlib
import Definitions.Def_SingularStopperVI_Penalised

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

/-- Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Theorem 5.3, p.22.
Problem C has a solution. The constructed solution also satisfies the bound (4.18) with one constant
`K₃`, since it is a locally uniform limit of solutions of Problem B (used at the end of the proof of
Theorem 6.1, p.31, and in the proof of Theorem 6.2, p.32). -/
theorem theorem_5_3 {Ω : Type*} [MeasurableSpace Ω] {d d' : ℕ} (B : Basis d' Ω) (hB : B.IsValid)
    (D : Data d d') (hD : D.Standing) (h31 : Assumption31 D) {α K0 K1 K2 : ℝ} {Jg : Jet d}
    (h32 : Assumption32 D α Jg K0 K1 K2)
    {ψ : ℝ → ℝ → ℝ} (hψ : IsPenalty ψ) :
    ∃ K3 : ℝ, 0 < K3 ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ u K,
      IsProblemC D ψ α ε δ u K ∧
      ∀ z ∈ stateDomain d D.T, 0 ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ K3 * (1 + ‖z.2‖ ^ 2) := by sorry

end SingularStopperVI
