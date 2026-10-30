-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_binary_root_converse
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.binary_root_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:32:37.685144+00:00
-- url     : https://prove2.me/theorems/b0456bdb-7989-4c69-832c-a1db46d2500e
-- title:
--   Unnumbered bound (7.6): binary-root-fidelity converse
-- statement:
--   For $d,N\ge1$, set $b(x,y)=\sqrt{xy}+\sqrt{(1-x)(1-y)}$, the binary root fidelity. Then the physically optimized deterministic PBT squared entanglement fidelity obeys
--   $$F_d^*(N)\le b\left(\frac1{d^2},\frac1N+\left(1-\frac1N\right)\frac1{d^2}\right).$$
--   There is no further outer square root. This preserves the stronger bound preceding the relaxed finite converse in Theorem 7.5.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 52, Unnumbered bound (7.6): binary-root-fidelity converse

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Unnumbered Eq. (7.6), PDF p.52: the binary ROOT fidelity expression bounds
squared channel entanglement fidelity; there is no further outer square root. -/
theorem binary_root_converse (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    pbtOptimalFidelity d N ≤ binaryRoot ((d : ℝ)^2)⁻¹
      ((N : ℝ)⁻¹ + (1-(N : ℝ)⁻¹)*((d : ℝ)^2)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
