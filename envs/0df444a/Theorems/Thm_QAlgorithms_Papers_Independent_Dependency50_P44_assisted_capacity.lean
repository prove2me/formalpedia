-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_assisted_capacity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.assisted_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:29:35.091352+00:00
-- url     : https://prove2.me/theorems/7db42e9c-96cc-4100-b771-fad0f5a21e91
-- title:
--   Regularized assisted quantum capacity region
-- statement:
--   All registers are finite-dimensional nonzero complex Hilbert spaces with fixed orthonormal bases; dimensions need not be powers of two. Let $\mathcal N:A'\to B_1B_2$ be a memoryless quantum broadcast channel, realized by a fixed rectangular Stinespring isometry $U_{\mathcal N}:A'\to B_1B_2E$. Entropies are in bits and $\|\cdot\|_1$ is the unhalved trace norm. For any normalized pure $\phi^{A_1A_2A'D}$, with unrestricted auxiliaries and discarded purifier $D$, let $\psi=(\mathrm{id}\otimes U_{\mathcal N}\otimes\mathrm{id})\phi$. Write $I(A;B)=H(A)+H(B)-H(AB)$ and $I(A\rangle B)=H(B)-H(AB)$.
--
--   Quantum communication sends two independent inputs initially maximally entangled with inaccessible references, through a joint encoder and two local decoders without receiver communication. Success means vanishing trace distance to the joint product of both reference/decoded EPR pairs. Rates are $\log_2 M_i/n$, using arbitrary positive integer message dimensions $M_i$ and liminf rate bounds. The literal source codes retain a pure garbage target on the entire purified output; the separate CPTP presentation traces that garbage before measuring the joint EPR error. Only their asymptotic regions are identified. Assisted codes have free independent pairwise EPR assistance; unassisted codes have none. Capacity includes closure.
--
--   For $n\ge1$, let $\mathcal R_{E,n}$ be the union, over every auxiliary dimension and every normalized pure input $\phi^{A_1A_2(A')^nD}$, of the rate pairs satisfying
--
--   $$
--   0\le Q_i\le\frac{I(A_i;B_i^n)_\psi}{2n}\ (i=1,2),\qquad
--   Q_1+Q_2\le\frac{I(A_1;B_1^n)_\psi+I(A_2;B_2^n)_\psi-I(A_1;A_2)_\psi}{2n},
--   $$
--
--   where $\psi=(\mathrm{id}\otimes U_{\mathcal N}^{\otimes n}\otimes\mathrm{id})\phi$. Then
--
--   $$\mathcal C_E(\mathcal N)=\overline{\operatorname{conv}\!\left(\bigcup_{n\ge1}\mathcal R_{E,n}\right)}.$$
--
--   This is a capacity equality in both the literal purified source model and the arbitrary joint-CPTP/local-CPTP model. The closed hull implements the source's operational limiting convention; it does not assert attainment at a finite block length.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 6, Theorem 3 / Eq. (16), continued on p.7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF pp.6–7, Theorem 3, (16): equality with the regularized assisted region.
Printed convex hull is interpreted as CLOSED convex hull, consistently with p.2 and the
vanishing-delta converse. Both literal purified codes and reduced CPTP entanglement codes
are characterized: their equivalence is ASYMPTOTIC after dilation/padding, not at fixed error.
This closure correction requires independent moderation. -/
theorem assisted_capacity {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) :
    sourceQuantumCapacity N true = regularizedAssisted N ∧
      broadcastQuantumCapacity N true = regularizedAssisted N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
