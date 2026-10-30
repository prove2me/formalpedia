-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_quantum_communication_dimension
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.quantum_communication_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:28:36.013197+00:00
-- url     : https://prove2.me/theorems/3d3f39bf-1614-4d7b-9891-669bb2377f3e
-- title:
--   Corollary 7.2: quantum communication dimension lower bound
-- statement:
--   Let the input space $A$ have dimension $d\ge1$ and the transmitted register $B$ have dimension $d_0$. Let $\rho_{A'B'}$ be any finite-dimensional shared density operator, $\mathcal E:AA'\to B$ a channel and $\mathcal D:BB'\to A$ a channel. During encoding, $B'$ is untouched. Suppose their resulting channel has squared entanglement fidelity $1-\epsilon^2$, where $0\le\epsilon\le1$. Then
--   $$d_0\ge d(1-\epsilon^2).$$
--   This bounds the dimension actually transmitted, while allowing arbitrary shared entanglement and Bob's retained ancilla.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 50, Corollary 7.2: quantum communication dimension lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 7.2, PDF p.50: transmitted quantum dimension, with arbitrary finite
preshared entanglement and Bob ancilla preserved during encoding. -/
theorem quantum_communication_dimension (d d0 a b : ℕ) (hd : 1 ≤ d)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d × Fin a) (Fin d0)) (hE : IsChannel E)
    (D : Superop (Fin d0 × Fin b) (Fin d)) (hD : IsChannel D)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hF : pbtFidelity d (communicatedChannel rho E D) = 1-eps^2) :
    (d : ℝ)*(1-eps^2) ≤ (d0 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
