-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_broadcastFather_inner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.broadcastFather_inner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:26:08.952207+00:00
-- url     : https://prove2.me/theorems/f7ce3ebe-e11c-4c60-ba8a-d2bc265d0f86
-- title:
--   Entanglement-assisted broadcast father inner region
-- statement:
--   All registers are finite-dimensional nonzero complex Hilbert spaces with fixed orthonormal bases; dimensions need not be powers of two. Let $\mathcal N:A'\to B_1B_2$ be a memoryless quantum broadcast channel, realized by a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$. Entropies are in bits and $\|\cdot\|_1$ is the unhalved trace norm. For any normalized pure $\phi^{A_1A_2A'D}$, with unrestricted auxiliaries and discarded purifier $D$, let $\psi=(\mathrm{id}\otimes U_{\mathcal N}\otimes\mathrm{id})\phi$. Write $I(A;B)=H(A)+H(B)-H(AB)$ and $I(A\rangle B)=H(B)-H(AB)$.
--
--   Quantum communication sends two independent inputs initially maximally entangled with inaccessible references, through a joint encoder and two local decoders without receiver communication. Success means vanishing trace distance to the joint product of both reference/decoded EPR pairs. Rates are $\log_2 M_i/n$, using arbitrary positive integer message dimensions $M_i$ and liminf rate bounds. The literal source codes retain a pure garbage target on the entire purified output; the separate CPTP presentation traces that garbage before measuring the joint EPR error. Only their asymptotic regions are identified. Assisted codes have free independent pairwise EPR assistance; unassisted codes have none. Capacity includes closure.
--
--   Every nonnegative rate pair satisfying
--
--   $$
--   0\le Q_1\le\tfrac12 I(A_1;B_1)_\psi,\qquad
--   0\le Q_2\le\tfrac12 I(A_2;B_2)_\psi,\qquad
--   Q_1+Q_2\le\tfrac12\bigl[I(A_1;B_1)_\psi+I(A_2;B_2)_\psi-I(A_1;A_2)_\psi\bigr].
--   $$
--
--   is operationally achievable with unlimited pairwise entanglement. This inner region permits mixed reduced inputs through the unrestricted purifier $D$, and its boundary uses vanishing rate slack.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 4, Theorem 2 / Eq. (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.4, Theorem 2, (9): the entanglement-assisted broadcast father inner region.
The discarded purifier D is unrestricted. Boundary rates use vanishing slack. -/
theorem broadcastFather_inner {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b)
    (S : InputState 2 (BroadcastBasis a)) :
    fatherRegion (broadcastOutputDensity N.channel S) ⊆ sourceQuantumAchievable N true := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
