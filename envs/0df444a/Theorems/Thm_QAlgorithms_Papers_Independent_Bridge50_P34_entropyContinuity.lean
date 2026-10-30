-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_entropyContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.entropyContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:05:11.563233+00:00
-- url     : https://prove2.me/theorems/d4d51504-b9d0-40f2-aaae-a0fc1abde042
-- title:
--   Entropy continuity without a distance cutoff
-- statement:
--   Let $\rho,\sigma$ be density matrices on a finite complex system of positive dimension $d$. Let $S$ be von Neumann entropy in bits, $T(\rho,\sigma)=\operatorname{Tr}|\rho-\sigma|$ the full trace norm distance, and $e=\exp(1)$. Then
--
--   $$
--   |S(\rho)-S(\sigma)|\le T(\rho,\sigma)\log_2 d+\frac{\log_2 e}{e}.
--   $$
--
--   This version applies at every distance, retaining a dimension-independent additive constant.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 2, Unrestricted entropy continuity bound, (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF p.2, (3): unrestricted entropy continuity; the additive constant is
log_2(e)/e, not 1/e, and the trace distance is full. -/
theorem entropyContinuity {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) :
    |vnEntropy rho - vnEntropy sigma| ≤
      fullTraceDistance rho sigma * Real.logb 2 (Fintype.card I) +
        Real.logb 2 (Real.exp 1) / Real.exp 1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
