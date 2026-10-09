-- Prove2me | Theorems.Thm_RobustPoA_Repeated_theorem_3_3
-- name    : RobustPoA.Repeated.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:03.878535+00:00
-- url     : https://prove2.me/theorems/b7a7c58b-ba3f-48b4-8b78-a55d987f747d
-- title:
--   Theorem 3.3, p. 14 — repeated-play extension with positive comparison cost
-- statement:
--   Let $G$ be a cost-minimization game with nonnegative joint cost $C$ and finite robust price of anarchy $\rho(G)$. Suppose the outcome sequence $s^1,s^2,\ldots$ gives every player vanishing average external regret. For every comparison outcome $s'$ with $C(s')>0$, there is a function $\eta(T)\to0$ such that, for every horizon $T\geq1$,
--
--   $$\frac1T\sum_{t=1}^{T}C(s^t)\leq\bigl(\rho(G)+\eta(T)\bigr)C(s').$$
--
--   This transfers a smoothness bound to repeated joint play without assuming that the outcomes converge to an equilibrium.
--
--   **Formalization Note** The printed theorem omits $C(s')>0$, but its multiplicative bound fails at zero comparison cost: one player may incur cost 1 once, then cost 0 forever, producing vanishing regret and positive average cost at every finite horizon. The preceding paragraph's additive bound has no such restriction. The nonnegative objective is the paper's standing convention. $\rho(G)$ is the extended-real infimum; an admissible smoothness pair makes it finite here (with $C(s')>0$ it is a real number at least 1), which is the page's only non-vacuous case.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Theorem 3.3, §3.2, p. 14; corrected at C(s*) = 0

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

namespace RobustPoA.Repeated

/-- Theorem 3.3, with positive comparison cost needed for its multiplicative form. -/
theorem theorem_3_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ)
    (hC : ∀ s, 0 ≤ RobustPoA.Static.cost C s)
    (hsmooth : ∃ lam mu : ℝ, mu < 1 ∧ RobustPoA.Static.IsSmooth C lam mu)
    (seq : ℕ → ∀ i, S i) (hreg : VanishingRegret C seq)
    (s' : ∀ i, S i) (hpos : 0 < RobustPoA.Static.cost C s') :
    ∃ η : ℕ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) ∧
      ∀ T : ℕ, 1 ≤ T →
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
          (RobustPoA.Static.robustPoA C + η T) * RobustPoA.Static.cost C s' := by sorry

end RobustPoA.Repeated
