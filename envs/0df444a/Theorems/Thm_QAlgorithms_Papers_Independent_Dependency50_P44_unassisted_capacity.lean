-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_unassisted_capacity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.unassisted_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:30:27.801483+00:00
-- url     : https://prove2.me/theorems/16506b20-d796-4d01-be2f-b893e8277aa9
-- title:
--   Regularized unassisted simultaneous entanglement-transmission capacity
-- statement:
--   All registers are finite-dimensional nonzero complex Hilbert spaces with fixed orthonormal bases; dimensions need not be powers of two. Let $\mathcal N:A'\to B_1B_2$ be a memoryless quantum broadcast channel, realized by a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$. Entropies are in bits and $\|\cdot\|_1$ is the unhalved trace norm. For any normalized pure $\phi^{A_1A_2A'D}$, with unrestricted auxiliaries and discarded purifier $D$, let $\psi=(\mathrm{id}\otimes U_{\mathcal N}\otimes\mathrm{id})\phi$. Write $I(A;B)=H(A)+H(B)-H(AB)$ and $I(A\rangle B)=H(B)-H(AB)$.
--
--   Quantum communication sends two independent inputs initially maximally entangled with inaccessible references, through a joint encoder and two local decoders without receiver communication. Success means vanishing trace distance to the joint product of both reference/decoded EPR pairs. Rates are $\log_2 M_i/n$, using arbitrary positive integer message dimensions $M_i$ and liminf rate bounds. The literal source codes retain a pure garbage target on the entire purified output; the separate CPTP presentation traces that garbage before measuring the joint EPR error. Only their asymptotic regions are identified. Assisted codes have free independent pairwise EPR assistance; unassisted codes have none. Capacity includes closure.
--
--   For $n\ge1$, let $\mathcal R_{Q,n}$ be the union over all normalized pure $\phi^{A_1A_2(A')^nD}$ and all auxiliary dimensions of
--
--   $$0\le Q_1\le\frac1n I(A_1\rangle B_1^n)_\psi,\qquad
--   0\le Q_2\le\frac1n I(A_2\rangle B_2^n)_\psi,$$
--
--   where $\psi=(\mathrm{id}\otimes U_{\mathcal N}^{\otimes n}\otimes\mathrm{id})\phi$. Then the unassisted quantum capacity region is
--
--   $$\mathcal C_Q(\mathcal N)=\overline{\operatorname{conv}\!\left(\bigcup_{n\ge1}\mathcal R_{Q,n}\right)}.$$
--
--   The equality covers both literal source codes and arbitrary joint CPTP encoding with local CPTP decoding, positive message dimensions, and a joint decoded EPR target. This characterizes simultaneous entanglement transmission without preshared assistance. It gives no confidential classical capacity theorem.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 7, Theorem 4 / Eq. (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.7, Theorem 4, (20): equality with the regularized unassisted region.
The operational closure corrects the printed convex-hull wording, as for Theorem 3.
Both literal source codes and arbitrary joint-CPTP/local-CPTP entanglement-transmission codes
have this asymptotic region; no finite-epsilon identification of their two errors is asserted. -/
theorem unassisted_capacity {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) :
    sourceQuantumCapacity N false = regularizedUnassisted N ∧
      broadcastQuantumCapacity N false = regularizedUnassisted N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
