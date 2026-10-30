-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_channel_amortization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.channel_amortization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:04:31.386475+00:00
-- url     : https://prove2.me/theorems/fd55b920-0cff-403a-8b58-b2d19ea889f1
-- title:
--   Theorem III.2: channel amortization inequality
-- statement:
--   Let $T:M_{d_{A'}}\to M_{d_{B'}}$ be a quantum channel and let $\rho_{AA'B}$ be an arbitrary density matrix, with all four system dimensions positive and finite. For every finite real $\alpha\ge1$,
--
--   $$E_\alpha^{A:B'B}((\mathrm{id}_A\otimes T\otimes\mathrm{id}_B)(\rho))\le E_{\max}(T)+E_\alpha^{AA':B}(\rho).$$
--
--   The quantity $E_\alpha$ is the minimum sandwiched divergence in bits to separable density matrices across the indicated cut, with its relative-entropy value at $\alpha=1$. The channel quantity optimizes max-relative entanglement over every finite reference input. No separability condition is imposed on $\rho$.
--
--   This bounds the entanglement increase when the transmitted subsystem moves from Alice to Bob.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 10, Theorem III.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem III.2, PDF pp.10--11: arbitrary entangled input and both moving cuts. -/
theorem channel_amortization (T : Superop I J) (hT : IsChannel T)
    (alpha : ℝ) (halpha : 1 ≤ alpha) (rho : Mat ((A × I) × B))
    (hrho : IsDensityMatrix rho) :
    entanglementRenyi alpha (sendChannelRegister T rho) ≤
      channelEMax T + entanglementRenyi alpha rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
