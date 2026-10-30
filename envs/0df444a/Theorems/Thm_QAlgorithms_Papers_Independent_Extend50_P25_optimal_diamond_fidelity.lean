-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_optimal_diamond_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.optimal_diamond_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:23:18.315789+00:00
-- url     : https://prove2.me/theorems/ef2244cc-b41a-4c31-924f-651ee16bcd80
-- title:
--   Corollary 3.5: optimal diamond error versus entanglement fidelity
-- statement:
--   For integers $d,N\ge1$, optimize both deterministic PBT resource and POVM in the physical port-selection model. With squared entanglement fidelity and the full diamond norm,
--   $$\varepsilon_d^*(N)=2\bigl(1-F_d^*(N)\bigr).$$
--   This relates the optimal average and worst-case channel figures of merit; it is not an identity for every unsymmetrized protocol.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 17, Corollary 3.5: optimal diamond error versus entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 3.5, PDF p.17: a relation between the two physical OPTIMA,
with squared entanglement fidelity and full diamond norm. -/
theorem optimal_diamond_fidelity (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    optimalDiamondError d N = 2*(1-pbtOptimalFidelity d N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
