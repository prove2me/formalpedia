-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_averaged_port_projector_norm
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.averaged_port_projector_norm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:24:18.179517+00:00
-- url     : https://prove2.me/theorems/e63742c8-8521-499a-9c3f-a4e9d031fc30
-- title:
--   Remark 3.8: operator norm of the averaged port projector
-- statement:
--   For $d,N\ge1$, let $\phi^+_{AB_i}$ be the normalized maximally entangled projector between a $d$-dimensional register $A$ and port $B_i$. Put $T^{(N)}=N^{-1}\sum_{i=1}^N\phi^+_{AB_i}\otimes I_{B_i^c}$. Its Euclidean operator norm satisfies
--   $$\|T^{(N)}\|_\infty=\frac{N+d-1}{dN}.$$
--   This gives the largest eigenvalue of the actual averaged port projector, retaining its physical normalization.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 18, Remark 3.8: operator norm of the averaged port projector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Remark 3.8, PDF p.18: norm of the averaged physical EPR port projectors.
The denominator is the product d*N, not d^N. -/
theorem averaged_port_projector_norm (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    portOperatorNorm ((N : ℂ)⁻¹ • ∑ i : Fin N, portProjector d N i) =
      ((N : ℝ)+(d : ℝ)-1)/((d : ℝ)*(N : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
