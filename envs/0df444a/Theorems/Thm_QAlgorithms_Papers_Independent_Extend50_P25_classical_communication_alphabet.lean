-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_classical_communication_alphabet
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.classical_communication_alphabet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:29:42.079079+00:00
-- url     : https://prove2.me/theorems/f2735d10-37c9-4900-aff0-761fe7080a9e
-- title:
--   Corollary 7.3: classical communication alphabet lower bound
-- statement:
--   In the entanglement-assisted setting of Corollary 7.2, suppose the encoder $\mathcal E$ has diagonal output in the fixed classical basis, so the transmitted register is a classical alphabet of size $d_0$. If the implemented channel has squared entanglement fidelity $1-\epsilon^2$, with $0\le\epsilon\le1$, then
--   $$d_0\ge d^2(1-\epsilon^2)^2.$$
--   This strengthens the quantum-dimension constraint for classical communication without restricting the shared resource or decoder.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 50, Corollary 7.3: classical communication alphabet lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 7.3, PDF p.50: classical alphabet size, retaining arbitrary preshared
entanglement and decoder. The factor (1-eps^2) is SQUARED. -/
theorem classical_communication_alphabet (d d0 a b : ℕ) (hd : 1 ≤ d)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin d × Fin a) (Fin d0)) (hE : IsQC E)
    (D : Superop (Fin d0 × Fin b) (Fin d)) (hD : IsChannel D)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hF : pbtFidelity d (communicatedChannel rho E D) = 1-eps^2) :
    (d : ℝ)^2*(1-eps^2)^2 ≤ (d0 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
