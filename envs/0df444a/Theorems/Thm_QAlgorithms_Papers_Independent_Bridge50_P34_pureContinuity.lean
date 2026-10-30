-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_pureContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.pureContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:06:54.870267+00:00
-- url     : https://prove2.me/theorems/73f037ee-34bc-4c25-b4f6-b03bb48b0d52
-- title:
--   Pure-state entanglement continuity at arbitrary distance
-- statement:
--   Let $\psi,\phi$ be unit vectors on finite complex systems $A\otimes B$ of positive dimensions $d,d'$. Let $E$ be the bit entropy of the $A$ reduction and let $t$ be the full trace norm distance of their pure density matrices. With $e=\exp(1)$, at every distance
--
--   $$
--   |E(\psi)-E(\phi)|\le t\min\{\log_2 d,\log_2 d'\}+\frac{\log_2e}{e}.
--   $$
--
--   This is the unrestricted companion of (6), including the source's interchangeable subsystem labels.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 2, Pure-state entanglement continuity for arbitrary distance, (7)

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

/-- PDF p.2, (7): arbitrary joint distance, retaining log_2(e)/e. -/
theorem pureContinuity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (psi phi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    |vnEntropy (traceRight (pureDensity psi)) - vnEntropy (traceRight (pureDensity phi))| ≤
      fullTraceDistance (pureDensity psi) (pureDensity phi) *
        min (Real.logb 2 (Fintype.card A)) (Real.logb 2 (Fintype.card B)) +
      Real.logb 2 (Real.exp 1) / Real.exp 1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
