-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_robust_communication_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.robust_communication_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:12:55.760544+00:00
-- url     : https://prove2.me/theorems/c20cd2bd-90ac-43a0-a8db-8eb4298ab420
-- title:
--   Theorem 8 (seed paper result): robust quantum communication lower bound
-- statement:
--   Let $\phi,\psi$ be normalized finite-dimensional bipartite pure states. Suppose a deterministic protocol, with arbitrary local operations and disposal, has unconditional output $\sigma$ satisfying squared Uhlmann fidelity $F(\sigma,|\psi\rangle\langle\psi|)\ge1-\varepsilon$, where $0\le\varepsilon<1/4$. Its quantum communication cost is $C=\sum_i\log_2 d_i$. Put $\delta=(4\varepsilon)^{1/8}$, and let $\Delta_e$ be the joint eigenvalue-subset spread at retained mass at least $1-e$. Then
--
--   $$2C\ge\Delta_\delta(\psi_A)-\Delta(\phi_A)+2\log_2(1-\delta).$$
--
--   The subscript $A$ denotes Alice's reduction and $\Delta=\Delta_0$. This is the paper's central robust communication bound.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Theorem 8 (seed paper result): robust quantum communication lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section Operational

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- PDF p.5, Theorem 8: robust quantum lower bound. epsilon<1/4 is forced by
the source's smoothing and logarithm domains. -/
theorem robust_communication_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (epsilon cost : ℝ) (hzero : 0 ≤ epsilon) (hsmall : epsilon < 1 / 4)
    (hprotocol : QuantumPrepares phi psi epsilon cost) :
    2 * cost ≥ smoothSpread (aliceDensity psi) (smoothingError epsilon) -
      spread (aliceDensity phi) + 2 * logTwo (1 - smoothingError epsilon) := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
