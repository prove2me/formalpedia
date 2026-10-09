-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_8
-- name    : PrimalDualPricing.Regret.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:25:15.94883+00:00
-- url     : https://prove2.me/theorems/6079bb43-c24d-469b-9364-957617bb363c
-- title:
--   Lemma 8, p. 16 — when $z^*>0$, $\mathbb E|S(T)-nc|=O((\log n)^\epsilon n^{1/2})$ and (18)
-- statement:
--   Under Assumptions 1–2 and Remark 2, suppose $z^*>0$ (insufficient capacity). Let $S(T)$ be the total sales over the season under Algorithm 1 and $P_m(t)$ its price path. For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that for every $n\ge3$
--   $$\mathbb E\big[|S(T)-nc|\big]\le C(\log n)^\epsilon n^{1/2}\tag{17}$$
--   and
--   $$\mathbb E\bigg[\Big|\int_0^T\sum_{m=1}^M d_m(P_m(t))\,dt-c\Big|\bigg]\le C(\log n)^\epsilon n^{-1/2}.\tag{18}$$
--
--   The interpolation step of the last phase steers the total sales to within order $n^{1/2}$ of the inventory. This is what makes the regret $O(n^{-1/2})$ attainable when the inventory constraint binds.
--
--   **Formalization Note** $S$ is the uncapped sales process of the modified system of §4. Both random variables are asserted to be integrable, so the bounds cannot hold through Lean's convention that the integral of a non-integrable function is $0$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 16, Lemma 8, Eqs. (17)–(18)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 8 (Chen–Gallego, arXiv:1812.09234v3, p. 16). When `z* > 0`, the total sales `S(T)` of Algorithm 1
(in the modified system of §4, where the policy runs to `T`) satisfy
(17) `E[|S(T) − n c|] = O((log n)^ε n^{1/2})` and
(18) `E[|∫_0^T ∑_m d_m(P_m(t)) dt − c|] = O((log n)^ε n^{−1/2})`.
Under Assumptions 1–2 and Remark 2 with `z* > 0`, for every sufficiently small `ε > 0` there is `C`,
independent of `n`, such that for all `n ≥ 3` both random variables are integrable and their expectations
are at most `C (log n)^ε n^{1/2}` and `C (log n)^ε n^{−1/2}`. -/
theorem lemma_8 {M : ℕ} (S : Setting M) (hz : 0 < S.zstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          (Integrable (fun ω => |(S.totalSales eps n N S.T ω : ℝ) - (n : ℝ) * S.c|) ∧
            ∫ ω, |(S.totalSales eps n N S.T ω : ℝ) - (n : ℝ) * S.c|
              ≤ C * Real.log n ^ eps * (n : ℝ) ^ (1 / 2 : ℝ)) ∧
          (Integrable (fun ω => |S.demandIntegral eps n N S.T ω - S.c|) ∧
            ∫ ω, |S.demandIntegral eps n N S.T ω - S.c|
              ≤ C * Real.log n ^ eps * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end PrimalDualPricing.Regret
