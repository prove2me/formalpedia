-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_7
-- name    : PrimalDualPricing.Regret.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:13.98992+00:00
-- url     : https://prove2.me/theorems/3d8a67c0-af68-429d-afec-421693093df2
-- title:
--   Lemma 7, p. 15 — the sales $S(t_K)$ are within $2n^{3/4}(\log n)^{1+8\epsilon}$ of the fluid inventory level
-- statement:
--   Under Assumptions 1–2 and Remark 2, let $S(t)$ be the cumulative sales of all types under Algorithm 1 and $t_K=\sum_{k=1}^{K-1}\tau^{(k)}$. For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that for every $n\ge3$
--   $$\mathbb P\bigg(\Big|S(t_K)-n\sum_{k=1}^{K-1}\tau^{(k)}\sum_{m=1}^M d_m(p^*_m)\Big|>2n^{3/4}(\log n)^{1+8\epsilon}\bigg)\le C(\log n)^{-2}n^{-1/2}.$$
--
--   At the beginning of the last phase the sales miss the fluid level by at most order $n^{3/4}$, up to logarithms. This is the error the last phase must correct.
--
--   **Formalization Note** $S$ is the uncapped sales process of the modified system of §4, in which the policy runs to $T$ regardless of the inventory.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 15, Lemma 7

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 7 (Chen–Gallego, arXiv:1812.09234v3, p. 15). At the beginning `t_K` of phase `K`, the cumulative
sales satisfy
`P(|S(t_K) − n ∑_{k=1}^{K−1} τ^{(k)} ∑_m d_m(p*_m)| > 2 n^{3/4}(log n)^{1+8ε}) = O((log n)^{−2} n^{−1/2})`.
Under Assumptions 1–2 and Remark 2, for every sufficiently small `ε > 0` there is `C`, independent of `n`,
bounding this probability by `C (log n)^{−2} n^{−1/2}` for all `n ≥ 3`. -/
theorem lemma_7 {M : ℕ} (S : Setting M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          (ℙ {ω | 2 * (n : ℝ) ^ (3 / 4 : ℝ) * Real.log n ^ (1 + 8 * eps)
              < |(S.totalSales eps n N (startTime eps n (numPhases eps n)) ω : ℝ)
                - (n : ℝ) * (∑ k ∈ Finset.Ico 1 (numPhases eps n), tau eps n k)
                  * ∑ m, S.d m (S.pstar m)|}).toReal
            ≤ C * Real.log n ^ (-(2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end PrimalDualPricing.Regret
