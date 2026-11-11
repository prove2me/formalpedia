-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_fact_2_4
-- name    : PriceIgnorance.Pairwise.fact_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:33.398976+00:00
-- url     : https://prove2.me/theorems/3d4d0c0f-51d2-461e-a165-015a0333cbcf
-- title:
--   Fact 2.4 — mixtures of $k$-wise independent laws with equal marginals are $k$-wise independent
-- statement:
--   Let $D^{(1)},\dots,D^{(m)}$ be probability measures on $\mathbb R^n$ under each of which the coordinates are $k$-wise independent, all with the same coordinate marginals. Let $\lambda_1,\dots,\lambda_m\ge0$ with $\sum_j\lambda_j=1$. Then under the mixture
--   $$D=\sum_{j=1}^m\lambda_jD^{(j)}$$
--   the coordinates are $k$-wise independent.
--
--   In the proof of Theorem 3.1 this shows that the reweighted mixture $\widehat D$ built from the minimax solution is again a feasible ($k$-wise independent) joint law.
--
--   Differences from the source:
--   - encoding: k-wise independent distributions D(i); the convex combination D = Σ λ_i D(i) → probability measures on Fin n → ℝ whose coordinates are KWiseIndep; the measure Σ_j ofReal(λ_j) • D(j); reason: a joint distribution is a measure on ℝⁿ; sampling D(i) w.p. λ_i and then drawing gives this mixture
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Fact 2.4 (proof p. 24)

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_PriceIgnorance_Pairwise_Instance

open MeasureTheory ProbabilityTheory

namespace PriceIgnorance.Pairwise

/-- Fact 2.4 (p. 4): a convex combination `Σ_j λ_j D^{(j)}` of `k`-wise independent joint
distributions `D^{(1)}, …, D^{(m)}` on `ℝⁿ` with the same marginals is `k`-wise independent. -/
theorem fact_2_4 {n m : ℕ} (k : ℕ) (Dv : Fin m → Measure (Fin n → ℝ))
    (hprob : ∀ j, IsProbabilityMeasure (Dv j))
    (hmarg : ∀ j j' i, (Dv j).map (coord i) = (Dv j').map (coord i))
    (hk : ∀ j, LaconicBarrier.KWiseIndep (Dv j) coord k)
    (lam : Fin m → ℝ) (hlam0 : ∀ j, 0 ≤ lam j) (hlam1 : ∑ j, lam j = 1) :
    LaconicBarrier.KWiseIndep (∑ j, ENNReal.ofReal (lam j) • Dv j) coord k := by sorry

end PriceIgnorance.Pairwise
