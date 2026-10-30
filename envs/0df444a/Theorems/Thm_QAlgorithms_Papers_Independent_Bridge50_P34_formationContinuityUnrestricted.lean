-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_formationContinuityUnrestricted
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.formationContinuityUnrestricted
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:08:51.398591+00:00
-- url     : https://prove2.me/theorems/74cdc293-aa2c-40aa-b854-ae803c61f11d
-- title:
--   Unrestricted formation continuity with the proof-intended distance
-- statement:
--   Let $\rho,\sigma$ be density matrices on finite complex systems $A\otimes B$ of positive dimensions $d,d'$. Let $E_F$ denote formation in bits, let $F=\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$ be root fidelity, and set $\Delta=2\sqrt{1-F^2}$. For $e=\exp(1)$, without a distance cutoff,
--
--   $$
--   |E_F(\rho)-E_F(\sigma)|\le\min\{5\log_2d+4\log_2d',\,5\log_2d'+4\log_2d\}\,\Delta+\frac{2\log_2e}{e}.
--   $$
--
--   This is the unrestricted formation bound with either subsystem labeling.
--
--   **Formalization Note** As in corrected (18), $\Delta$ is the proof-intended purification distance, explicitly different from printed (10). The literal printed-distance version of (19) remains unverified by the source's argument.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 3, Unrestricted formation continuity bound, (19), with the proof-intended distance

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

/-- PDF p.3, (19), with proof-intended purification distance, no cutoff.
The source correction and symmetric dimension coefficient are explicit. -/
theorem formationContinuityUnrestricted {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    |formation rho - formation sigma| ≤
      min (5 * Real.logb 2 (Fintype.card A) + 4 * Real.logb 2 (Fintype.card B))
        (5 * Real.logb 2 (Fintype.card B) + 4 * Real.logb 2 (Fintype.card A)) *
        purificationDistance rho sigma + 2 * Real.logb 2 (Real.exp 1) / Real.exp 1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
