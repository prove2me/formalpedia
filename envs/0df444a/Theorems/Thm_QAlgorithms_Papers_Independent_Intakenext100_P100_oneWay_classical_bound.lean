-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_oneWay_classical_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.oneWay_classical_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:18:19.062729+00:00
-- url     : https://prove2.me/theorems/600545f2-488d-4eec-90dc-a3603419a0df
-- title:
--   One-way classical communication bound
-- statement:
--   Let $\rho$ be any bipartite density matrix with positive finite local dimensions, and let $l\ge0$ be an integer. Let $\rho'$ be the actual output of any Alice-to-Bob one-round classical protocol with at most $2^l$ message values, arbitrary local quantum operations and local ancillary systems, and no additional initially correlated resource. All retained records count as part of the output. Then
--   $$I_c(\rho)\ge2^{-l}\bigl(I_c(\rho')-l\bigr),\qquad I_c^{(l)}(\rho)-I_c(\rho)\le l+(2^l-1)I_c(\rho).$$
--   The superscript denotes optimization over these one-way protocols and all positive finite output dimensions. This bounds locking by the message alphabet and the initial measured correlation.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Theorem 1: every actual one-way l-bit protocol, followed by
its optimized consequence. No interactive classical protocol is optimized here. -/
theorem oneWay_classical_bound {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (l : ℕ) (P : OneWayMap A B C D l) :
    lockingMeasuredInformation rho ≥ ((2 : ℝ)^l)⁻¹ *
      (lockingMeasuredInformation (oneWayOutput P rho) - (l : ℝ)) ∧
    oneWayInformation l rho - lockingMeasuredInformation rho ≤
      (l : ℝ) + ((2 : ℝ)^l - 1) * lockingMeasuredInformation rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
