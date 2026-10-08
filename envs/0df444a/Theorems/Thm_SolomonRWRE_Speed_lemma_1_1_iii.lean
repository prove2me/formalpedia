-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_lemma_1_1_iii
-- name    : SolomonRWRE.Speed.lemma_1_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:09.297042+00:00
-- url     : https://prove2.me/theorems/f89433f3-21e4-4a5b-8a2d-1cbf4dba5338
-- title:
--   Lemma (1.1)(iii) — fixed-environment mean passage time
-- statement:
--   Fix an environment $a=(a_z)_{z\in\mathbb Z}$ with $0<a_z<1$, and start its nearest-neighbor chain at zero. Write $\sigma_z=(1-a_z)/a_z$. If the chain reaches $1$ with probability one, then its mean first passage time $m_{01}=E_a T_1$ is
--
--   $$
--   m_{01}=(1+\sigma_0)+\sum_{j=-\infty}^{0}(1+\sigma_{j-1})\sigma_j\cdots\sigma_0.
--   $$
--
--   The identity expresses a fixed-environment hitting time through the ratios of left- and right-step probabilities. Either side may be infinite.
--
--   **Formalization Note** The bilateral index is written as $j=-n$ with $n\ge0$ in Lean; all terms and the integral are extended nonnegative.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 2–3, Lemma (1.1)(iii), display (1.4)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 3, Lemma (1.1)(iii), display (1.4). The series is
indexed by `j = -n`, for `n ≥ 0`. **Formalization Note:** its terms and the
mean passage time are extended nonnegative, so the identity includes infinity. -/
theorem lemma_1_1_iii {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (a : ℤ → ℝ) (X : ℕ → Ω → ℤ) (hα : ∀ n, 0 < a n ∧ a n < 1)
    (hchain : SolomonRWRE.Recurrence.IsChainInEnv P a 0 X)
    (hf : P {ω | ∃ k : ℕ, 0 < k ∧ X k ω = 1} = 1) :
    (∫⁻ ω, ENat.toENNReal (passageTime X 1 ω) ∂P) =
      (1 + sigmaFixed a 0) +
      ∑' n : ℕ, (1 + sigmaFixed a (-(n : ℤ) - 1)) *
        ∏ k ∈ Finset.range (n + 1), sigmaFixed a (-(k : ℤ)) := by sorry

end SolomonRWRE.Speed
