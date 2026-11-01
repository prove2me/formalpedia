-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_classical_communication_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.classical_communication_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:14:19.293061+00:00
-- url     : https://prove2.me/theorems/61424885-defb-43b1-8bb6-849452932c60
-- title:
--   Corollary 10: classical communication lower bound
-- statement:
--   Let $\phi,\psi$ be normalized bipartite pure states. A deterministic finite LOCC protocol, optionally supplied with any finite number $k$ of EPR pairs, produces an unconditional output with squared fidelity at least $1-\varepsilon$ to $\psi$, where $0\le\varepsilon<1/4$. If its worst-case classical communication is $C$ bits, and $\delta=(4\varepsilon)^{1/8}$, then
--
--   $$C\ge\Delta_\delta(\psi_A)-\Delta(\phi_A)+2\log_2(1-\delta).$$
--
--   Here $\Delta_e$ is joint eigenvalue-subset smoothing of the spectral spread. The formal model counts log-alphabet message sizes and includes binary messages. This is the factor-two improvement over quantum communication.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Corollary 10: classical communication lower bound

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

/-- PDF p.5, Corollary 10: classical-only communication improves the factor two;
arbitrary finite EPR supplementation is allowed, including k=0. -/
theorem classical_communication_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (k : ℕ) (epsilon cost : ℝ) (hzero : 0 ≤ epsilon) (hsmall : epsilon < 1 / 4)
    (hprotocol : ClassicalPrepares (tensorPureStates phi (eprPairs k)) psi epsilon cost) :
    cost ≥ smoothSpread (aliceDensity psi) (smoothingError epsilon) -
      spread (aliceDensity phi) + 2 * logTwo (1 - smoothingError epsilon) := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
