-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_cauchy_schwarz_4_10
-- name    : PoissonDepTrials.MixInv.cauchy_schwarz_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:16:07.2471+00:00
-- url     : https://prove2.me/theorems/6af996ae-5966-4742-a570-14e7e7c65b65
-- title:
--   (4.10), proof of Lemma 4.5, p. 540 — ΣΣ_{|i−j|≤m} p_ip_j ≤ (2m + 1)Σ p_i²
-- statement:
--   Let $p_i=P(X_i=1)$ for random variables $X_1,\dots,X_n$ and let $m\ge0$. Then
--   $$\sum\sum_{|i-j|\le m}p_ip_j\le(2m+1)\sum_{i=1}^np_i^2,$$
--   where the double sum runs over $i,j\in\{1,\dots,n\}$. The paper obtains it from the Cauchy–Schwarz inequality; it converts the $p_ip_j$ terms of (4.7) and (4.19) into $\sum p_i^2$.
--
--   **Formalization Note** No hypothesis on the trials is needed: the inequality holds for any reals $p_i$; here $p_i$ is the definition `prob`.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, proof of Lemma 4.5, (4.10)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem cauchy_schwarz_4_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (X : ℕ → Ω → ℕ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m, prob P X i * prob P X j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 := by sorry

end PoissonDepTrials.MixInv
