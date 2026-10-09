-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_primal_dual_regret_bound
-- name    : PrimalDualPricing.Regret.primal_dual_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:31.563645+00:00
-- url     : https://prove2.me/theorems/30b130ff-07d8-4eee-99ce-4f15f5ab485b
-- title:
--   Theorem 1, p. 17 — the primal-dual learning algorithm has regret $R^\pi_n(T,c)\le C(\log n)^{2+\delta}n^{-1/2}$
-- statement:
--   A firm sells $c\,n$ units of a product over a season $[0,T]$ to $M\ge1$ types of consumers. Type-$m$ consumers arrive as a Poisson process with rate $n\,d_m(p)$ when charged $p$. The demand functions are unknown to the firm. They satisfy Assumption 1, and the optimal fluid prices $p^*_m$ and dual variable $z^*$ lie in known intervals (Assumption 2, with Remark 2).
--
--   **Theorem 1.** For any $\delta>0$ one can select $\epsilon>0$ such that the primal-dual learning algorithm (Algorithm 1 with parameter $\epsilon$) satisfies
--   $$R^\pi_n(T,c)=1-\frac{J^\pi_n(T,c)}{J^D_n(T,c)}\le C(\log n)^{2+\delta}n^{-1/2}\qquad\text{for all }n\ge3,$$
--   where the constant $C$ is independent of $n$. Here $J^\pi_n$ is the expected revenue of the algorithm in the $n$-th system, and $J^D_n$ the fluid value with demand $n\,d_m$ and inventory $nc$.
--
--   Up to logarithmic factors this matches the $n^{-1/2}$ lower bound known for a single type (Besbes and Zeevi, 2009), and the rate does not depend on the number of types $M$.
--
--   **Formalization Note** The order of quantifiers is: model, then $\delta$, then $\epsilon$, then $C$, then the probability space with $M$ independent unit-rate Poisson processes (right-continuous, jointly measurable), then $n\ge3$. $C$ is chosen before the probability space, which is stronger than "independent of $n$"; it is correct because the regret depends only on the law of the arrival processes. The real system holds $\lfloor nc\rfloor$ units and sells nothing after the stock-out. The algorithm's decisions use only $T$, $c$, $n$, $\epsilon$, the intervals of Assumption 2 and the observed sales. Assumption 2 is read with $z^*\in[0,\overline z)$ instead of the printed $(0,\overline z)$, so the theorem covers both capacity regimes. For each fixed $n$ the regret is finite, so "for all $n\ge3$" is equivalent to "for all sufficiently large $n$".
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 17, Theorem 1

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (Chen–Gallego, arXiv:1812.09234v3, p. 17). Suppose Assumptions 1 and 2 hold (with Remark 2;
`Setting`) and there are `M ≥ 1` consumer types. For any `δ > 0` one can select `ε > 0` such that the regret
of the primal-dual learning algorithm (Algorithm 1 with parameter `ε`) satisfies
`R^π_n(T, c) ≤ C (log n)^{2+δ} n^{−1/2}` for every `n ≥ 3`, where the constant `C` is independent of `n`
(and of the probability space carrying the `M` independent unit-rate Poisson arrival processes). -/
theorem primal_dual_regret_bound {M : ℕ} (hM : 0 < M) (S : Setting M) :
    ∀ δ : ℝ, 0 < δ → ∃ eps : ℝ, 0 < eps ∧ ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          S.regret eps n N ≤ C * Real.log n ^ (2 + δ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end PrimalDualPricing.Regret
