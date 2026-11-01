-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_direct_sampling_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.direct_sampling_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:17:47.427361+00:00
-- url     : https://prove2.me/theorems/493e5123-3daa-4066-a71f-cd241c795db1
-- title:
--   Direct random-pair verification requires exponential resources
-- statement:
--   Let $N\ge1$ and $0\le m<N$. Among $N$ pairs, exactly one fixed pair is a nonsinglet and all others are singlets. Test a uniformly chosen $m$-element subset. Write $p_{\rm miss}$ for the probability the nonsinglet remains untested. Then
--
--   $$p_{\rm miss}=\frac{N-m}{N}\ge\frac1N.$$
--
--   For $k\ge0$, the requirement $p_{\rm miss}\le e^{-k}$ therefore entails $N\ge e^k$ and $m\ge(1-e^{-k})N$. This is a resource lower bound for this direct-testing scheme.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 7, Direct random-pair verification requires exponential resources

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.7: the direct scheme needs exponentially many pairs to make its
one-defective-pair cheating probability at most exp(-k); m=N is excluded. -/
theorem direct_sampling_cost (N m : ℕ) (hm : m < N) (bad : Fin N) :
    directMissProbability N m bad = (N - m : ℕ) / (N : ℝ) ∧
    1 / (N : ℝ) ≤ directMissProbability N m bad ∧
    ∀ k : ℝ, 0 ≤ k → directMissProbability N m bad ≤ Real.exp (-k) →
      Real.exp k ≤ (N : ℝ) ∧
      (1 - Real.exp (-k)) * (N : ℝ) ≤ (m : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
