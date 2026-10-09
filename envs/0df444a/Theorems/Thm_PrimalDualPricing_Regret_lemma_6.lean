-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_6
-- name    : PrimalDualPricing.Regret.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:16.353011+00:00
-- url     : https://prove2.me/theorems/c138a5ff-2358-4ecc-b0e9-7fa5e72cd1f3
-- title:
--   Lemma 6, p. 15 — the integrated demand rate at $t_K$ is within $n^{-1/4}(\log n)^{1+8\epsilon}$ of its fluid value
-- statement:
--   Under Assumptions 1–2 and Remark 2, let $P_m(t)$ be the price path of Algorithm 1 and $t_K=\sum_{k=1}^{K-1}\tau^{(k)}$ the beginning of the last phase. For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that for every $n\ge3$
--   $$\mathbb P\bigg(\Big|\int_0^{t_K}\sum_{m=1}^M d_m(P_m(t))\,dt-\sum_{k=1}^{K-1}\tau^{(k)}\sum_{m=1}^M d_m(p^*_m)\Big|>n^{-1/4}(\log n)^{1+8\epsilon}\bigg)\le\frac{C(\log n)^2}{n}.$$
--
--   $n\int_0^{t_K}\sum_m d_m(P_m(t))\,dt$ is the conditional mean of the sales $S(t_K)$ given the prices. The lemma compares it with the fluid inventory level at $t_K$.
--
--   **Formalization Note** The integral is pathwise along the algorithm's piecewise-constant price path, a finite sum.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 15, Lemma 6

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 6 (Chen–Gallego, arXiv:1812.09234v3, p. 15). At the beginning `t_K` of phase `K`,
`P(|∫_0^{t_K} ∑_m d_m(P_m(t)) dt − ∑_{k=1}^{K−1} τ^{(k)} ∑_m d_m(p*_m)| > n^{−1/4}(log n)^{1+8ε}) = O((log n)² n^{−1})`,
where `P_m(t)` is the price path of Algorithm 1. Under Assumptions 1–2 and Remark 2, for every sufficiently
small `ε > 0` there is `C`, independent of `n`, bounding this probability by `C (log n)² / n` for all
`n ≥ 3`. -/
theorem lemma_6 {M : ℕ} (S : Setting M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          (ℙ {ω | (n : ℝ) ^ (-(1 / 4 : ℝ)) * Real.log n ^ (1 + 8 * eps)
              < |S.demandIntegral eps n N (startTime eps n (numPhases eps n)) ω
                - (∑ k ∈ Finset.Ico 1 (numPhases eps n), tau eps n k)
                  * ∑ m, S.d m (S.pstar m)|}).toReal
            ≤ C * Real.log n ^ 2 / n := by sorry

end PrimalDualPricing.Regret
