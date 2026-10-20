-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_assisted_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.assisted_classical_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:33:48.119367+00:00
-- url     : https://prove2.me/theorems/6b0e3d06-7401-41bc-be61-5327f012cc7e
-- title:
--   Assisted classical father region and regularized capacity
-- statement:
--   All registers are finite-dimensional nonzero complex Hilbert spaces with fixed orthonormal bases; dimensions need not be powers of two. Let $\mathcal N:A'\to B_1B_2$ be a memoryless quantum broadcast channel, realized by a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$. Entropies are in bits and $\|\cdot\|_1$ is the unhalved trace norm. For any normalized pure $\phi^{A_1A_2A'D}$, with unrestricted auxiliaries and discarded purifier $D$, let $\psi=(\mathrm{id}\otimes U_{\mathcal N}\otimes\mathrm{id})\phi$. Write $I(A;B)=H(A)+H(B)-H(AB)$ and $I(A\rangle B)=H(B)-H(AB)$.
--
--   For classical communication, use independent uniform finite messages, arbitrary message-dependent CPTP preparation, free independent pairwise entanglement, local receiver POVMs, and vanishing average joint decoding error. Rates are liminf $\log_2 M_i/n$ and capacity includes closure. For every $\phi$ as above, all nonnegative rates satisfying
--
--   $$C_i\le I(A_i;B_i)_\psi\ (i=1,2),\qquad
--   C_1+C_2\le I(A_1;B_1)_\psi+I(A_2;B_2)_\psi-I(A_1;A_2)_\psi$$
--
--   are operationally achievable. Moreover, if $\mathcal R_E^{\rm reg}(\mathcal N)$ is the closed convex hull of the complete block-regularized quantum father region (16),
--
--   $$\mathcal C_{E,\mathrm{classical}}(\mathcal N)
--   =\{(2Q_1,2Q_2):(Q_1,Q_2)\in\mathcal R_E^{\rm reg}(\mathcal N)\}.$$
--
--   This states the conversion via superdense coding and the matching regularized optimality. No secrecy or receiver/environment leakage requirement is present.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 1, Abstract / I, superdense coding and regularized optimality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.1, abstract and I: coordinatewise doubling of the father region is achievable for
assisted classical communication, and its regularization is the entire classical capacity.
The usual uniform independent messages and average joint error are made explicit in the
operational definition. This states no confidential or secret-message coding theorem. -/
theorem assisted_classical_capacity {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) :
    (∀ S : InputState 2 (BroadcastBasis a), ∀ q ∈ fatherRegion (broadcastOutputDensity N.channel S),
      (fun j => 2 * q j) ∈ classicalAchievable N) ∧
    assistedBroadcastClassicalCapacity N = {c | (fun j => c j / 2) ∈ regularizedAssisted N} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
