-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_parallel_inversion_bounds
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.parallel_inversion_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:13:34.302878+00:00
-- url     : https://prove2.me/theorems/549940bc-d062-4c94-90b1-1f7b9758bbbf
-- title:
--   Parallel inverse construction and universal parallel bound
-- statement:
--   Let $d\ge2$ and $k\ge0$ be integers, and put $k'=\lfloor k/(d-1)\rfloor$. A fixed delayed parallel circuit implements the inverse channel of every $U\in U(d)$ exactly with constant success probability
--
--   $$p_S=1-\frac{d^2-1}{k'+d^2-1}.$$
--
--   Every universal parallel inversion circuit with $k$ oracle slots and constant success probability $p$ obeys
--
--   $$p\le1-\frac{d^2-1}{k(d-1)+d^2-1}.$$
--
--   Unused oracle slots can be discarded. For $k<d-1$ the construction has zero success; the dimension-one identity-channel case is outside the divided construction.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 18, Theorem 4, both columns

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.18, Theorem 4, including the top-right-column continuation: parallel
inverse construction uses floor(k/(d-1)) groups, and the upper bound covers ALL
parallel circuits. Extra uses can be padded and discarded. -/
theorem parallel_inversion_bounds {d k : ℕ} (hd : 2 ≤ d) :
    DelayedAttainable d k (targetChoi .inverse)
      (parallelTransposeProbability d (k / (d-1))) ∧
    ∀ p, Attainable .parallel d k (targetChoi .inverse) p →
      p ≤ parallelTransposeProbability d (k*(d-1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
