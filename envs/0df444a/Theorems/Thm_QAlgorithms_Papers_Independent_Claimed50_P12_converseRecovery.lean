-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_converseRecovery
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.converseRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:41:24.520951+00:00
-- url     : https://prove2.me/theorems/083c8313-bf96-4c07-9332-f6e7a3ee9275
-- title:
--   Converse bounds for every recovery channel
-- statement:
--   Let $\rho_{ABC}$ be a density operator on nonzero finite-dimensional complex Hilbert spaces. For any CPTP map $T:B\to BC$, put $\sigma=(\mathrm{id}_A\otimes T)(\rho_{AB})$, $\Delta=\tfrac12\|\rho-\sigma\|_1$ and $d_A=\dim A$. With all entropies in bits, if $\Delta\le1/2$, then
--
--   $$I(A:C\mid B)_\rho\le8\Delta\log_2d_A-4\Delta\log_2(2\Delta)-2(1-2\Delta)\log_2(1-2\Delta).$$
--
--   For all distances, one also has
--
--   $$I(A:C\mid B)_\rho\le7\log_2d_A\sqrt\Delta.$$
--
--   The convention $0\log_2 0=0$ is by continuity; the $d_A=1$ case gives zero. These are converse bounds for each channel, without optimizing over recovery maps.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 3, ConverseRecovery

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Converse recovery, Eq.8 and Eq.10 (PDF p.3), for EVERY reconstruction channel.
Only the Eq.8 clause requires generalizedTraceDistance <= 1/2. Endpoint x log x is zero by continuity. -/
theorem converseRecovery {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho)
    (T : Superop B (B × C)) (hT : IsChannel T) :
    let distance := generalizedTraceDistance rho (idTensorSuperop T (marginalAB rho))
    (distance ≤ 1/2 → cmi rho ≤
      8 * distance * Real.logb 2 (Fintype.card A : ℝ) -
      4 * distance * Real.logb 2 (2 * distance) -
      2 * (1-2*distance) * Real.logb 2 (1-2*distance)) ∧
    cmi rho ≤ 7 * Real.logb 2 (Fintype.card A : ℝ) * Real.sqrt distance := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
