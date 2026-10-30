-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_piecewise_converses
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.piecewise_converses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:19:38.883818+00:00
-- url     : https://prove2.me/theorems/12c40be7-c216-4337-a984-d6b03e1241e0
-- title:
--   Corollary 1.6: piecewise fidelity and diamond converses
-- statement:
--   Let $d,N\ge1$ be integers. Optimize over the same physical deterministic PBT protocols to obtain squared fidelity $F_d^*(N)$ and full diamond error $\varepsilon_d^*(N)$. Then
--   $$F_d^*(N)\le\begin{cases}\sqrt N/d&N\le d^2/2,\1-(d^2-1)/(16N^2)&N>d^2/2,\end{cases}$$
--   $$\varepsilon_d^*(N)\ge\begin{cases}2(1-\sqrt N/d)&N\le d^2/2,\2(d^2-1)/(16N^2)&N>d^2/2.\end{cases}$$
--   These simultaneous converse bounds apply at every finite port count.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 6, Corollary 1.6: piecewise fidelity and diamond converses

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 1.6, PDF p.6 (restated p.52): BOTH fidelity and full diamond converses.
The boundary N=d^2/2 belongs to the first branch. -/
theorem piecewise_converses (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    pbtOptimalFidelity d N ≤
      (if (N : ℝ) ≤ (d : ℝ)^2/2 then Real.sqrt (N : ℝ)/d
       else 1 - ((d : ℝ)^2-1)/(16*(N : ℝ)^2)) ∧
    optimalDiamondError d N ≥
      (if (N : ℝ) ≤ (d : ℝ)^2/2 then 2*(1-Real.sqrt (N : ℝ)/d)
       else 2*((d : ℝ)^2-1)/(16*(N : ℝ)^2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
