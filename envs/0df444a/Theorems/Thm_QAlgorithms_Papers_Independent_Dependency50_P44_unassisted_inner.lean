-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_unassisted_inner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.unassisted_inner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:28:40.267211+00:00
-- url     : https://prove2.me/theorems/146fe497-8c6f-4e1a-8678-4debe8f809e1
-- title:
--   Unassisted coherent-information inner rectangle
-- statement:
--   All registers are finite-dimensional nonzero complex Hilbert spaces with fixed orthonormal bases; dimensions need not be powers of two. Let $\mathcal N:A'\to B_1B_2$ be a memoryless quantum broadcast channel, realized by a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$. Entropies are in bits and $\|\cdot\|_1$ is the unhalved trace norm. For any normalized pure $\phi^{A_1A_2A'D}$, with unrestricted auxiliaries and discarded purifier $D$, let $\psi=(\mathrm{id}\otimes U_{\mathcal N}\otimes\mathrm{id})\phi$. Write $I(A;B)=H(A)+H(B)-H(AB)$ and $I(A\rangle B)=H(B)-H(AB)$.
--
--   Quantum communication sends two independent inputs initially maximally entangled with inaccessible references, through a joint encoder and two local decoders without receiver communication. Success means vanishing trace distance to the joint product of both reference/decoded EPR pairs. Rates are $\log_2 M_i/n$, using arbitrary positive integer message dimensions $M_i$ and liminf rate bounds. The literal source codes retain a pure garbage target on the entire purified output; the separate CPTP presentation traces that garbage before measuring the joint EPR error. Only their asymptotic regions are identified. Assisted codes have free independent pairwise EPR assistance; unassisted codes have none. Capacity includes closure.
--
--   Without any preshared entanglement, every rate pair in
--
--   $$0\le Q_1\le I(A_1\rangle B_1)_\psi,\qquad 0\le Q_2\le I(A_2\rangle B_2)_\psi$$
--
--   is operationally achievable. There is no separate sum-rate constraint. A state with either negative coherent information contributes an empty rectangle. This gives the unassisted coding region; entanglement startup and recycling are construction ingredients rather than assistance hypotheses. Finite convex combinations of these state-specific rectangles are achievable by time sharing.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 6, VI.A, unnumbered displayed region

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.6, VI.A: the unassisted coherent-information rectangle. No initial entanglement
is granted, no positive part replaces negative coherent information, and no sum bound is added.
The finite convex hull over input states retains the source's explicit time-sharing conclusion. -/
theorem unassisted_inner {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) :
    convexHull ℝ {q | ∃ S : InputState 2 (BroadcastBasis a),
      q ∈ coherentRegion (broadcastOutputDensity N.channel S)} ⊆ sourceQuantumAchievable N false := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
