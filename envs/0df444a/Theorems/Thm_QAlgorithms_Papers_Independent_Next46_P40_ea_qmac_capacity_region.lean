-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_ea_qmac_capacity_region
-- name    : QAlgorithms.Papers.Independent.Next46.P40.ea_qmac_capacity_region
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:48:25.823896+00:00
-- url     : https://prove2.me/theorems/631805b3-8d00-4f02-aab0-3f3a093a6bf8
-- title:
--   Entanglement-assisted QMAC capacity region
-- statement:
--   Let $\mathcal M:A'B'\to C$ be a memoryless CPTP channel between finite nonzero registers. Alice and Bob have independent pure entangled resources with Charlie. A block code uses local CPTP encoders and a joint receiver POVM, chosen before both messages, and has maximum joint error at most $\epsilon$. A nonnegative pair is achievable if, for every $\epsilon,\delta>0$, all sufficiently large positive blocklengths admit such a code with integer message counts $M_i$ satisfying $\log_2 M_i\ge n(R_i-\delta)$. Let $C_E(\mathcal M)$ be the closure of these achievable pairs.
--
--   For independent normalized purifications $\phi_1^{AA'}$ and $\phi_2^{BB'}$, set $\theta=(\mathrm{id}_{AB}\otimes\mathcal M)(\phi_1\otimes\phi_2)$. Let $\widetilde C_E(\mathcal M)$ be the union, over these inputs, of the nonnegative pairs satisfying $R_1\le I(A;C\mid B)_\theta$, $R_2\le I(B;C\mid A)_\theta$ and $R_1+R_2\le I(AB;C)_\theta$. Then
--
--   $$C_E(\mathcal M)=\overline{\bigcup_{n\ge1}\frac1n\widetilde C_E(\mathcal M^{\otimes n})}.$$
--
--   Each sender's block input may be entangled across uses; independence is imposed between senders. Entropies are in bits. The equality characterizes the operational capacity region without an additional convex-hull operation.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 6, Theorem 6, (42)–(44)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF pp.6--9, Theorem 6, (42)--(44); p.7 specifies that the bar is closure.
Codes have independent sender-receiver resources, local CPTP encoders and
maximum error. Inputs may have correlations within each sender's block. -/
theorem ea_qmac_capacity_region
    [Nonempty A] [Nonempty B] [Nonempty C]
    (M : Superop (A × B) C) (hM : IsChannel M) :
    eaMacCapacityRegion M = regularizedEAMacRegion M := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
