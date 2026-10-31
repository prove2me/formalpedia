-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_parallel_transposition_optimal
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.parallel_transposition_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:09:57.87287+00:00
-- url     : https://prove2.me/theorems/b729c7b5-56ad-49e5-8bed-2080aea161c8
-- title:
--   Attained optimum for parallel transpose
-- statement:
--   For integers $d,k\ge1$, there is a delayed parallel $k$-slot instrument that implements the transpose channel of every $U\in U(d)$ exactly with constant probability
--
--   $$p_T(d,k)=1-\frac{d^2-1}{k+d^2-1}.$$
--
--   Every parallel universal transpose instrument with constant success probability $p$ satisfies $p\le p_T(d,k)$. Thus the value is attained, even with delayed input.
--
--   The source realizes this optimum by modified port-based gate teleportation. The fraction is rational; it is not a binomial coefficient.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 16, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.13–16, Theorem 2: the rational optimum is attained with delayed input
and bounds every parallel protocol, for every unknown U. -/
theorem parallel_transposition_optimal {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    DelayedAttainable d k (targetChoi .transpose) (parallelTransposeProbability d k) ∧
    ∀ p, Attainable .parallel d k (targetChoi .transpose) p →
      p ≤ parallelTransposeProbability d k := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
