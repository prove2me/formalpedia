-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_port_count_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.port_count_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:30:30.414671+00:00
-- url     : https://prove2.me/theorems/c4ed000f-7d0e-433b-a636-2b85b159eded
-- title:
--   Corollary 7.4: port count versus entanglement fidelity
-- statement:
--   For integers $d,N\ge1$, every deterministic PBT protocol, allowing arbitrary resource and Alice measurement but only Bob's port selection, obeys
--   $$F_d^*(N)\le\frac{\sqrt N}{d},$$
--   where $F_d^*(N)$ is the supremum over that physical model. This is the port-alphabet consequence of the classical communication bound.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 50, Corollary 7.4: port count versus entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 7.4, PDF p.50: bound on the constructed optimum, hence every PBT protocol. -/
theorem port_count_fidelity (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    pbtOptimalFidelity d N ≤ Real.sqrt (N : ℝ)/(d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
