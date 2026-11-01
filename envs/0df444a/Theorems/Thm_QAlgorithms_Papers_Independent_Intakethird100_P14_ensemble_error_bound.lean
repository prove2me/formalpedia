-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_ensemble_error_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.ensemble_error_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:56:29.877677+00:00
-- url     : https://prove2.me/theorems/4d753797-fec6-4317-ab07-d50f05f8470d
-- title:
--   Average ensemble error and existence of a good frozen vector
-- statement:
--   Let $W$ be any binary-input classical–quantum channel with positive trace-one density outputs, let $N=2^n$, and let $A\subseteq\{1,\ldots,N\}$ be an arbitrary information set, with $K=|A|$. Encode by $G_N$ and use the prescribed collective successive cancellation decoder: square-root-density spectral tests at information positions, identity at frozen positions, and uniform unknown future bits. Write $P_e(N,K,A,f)$ for block error averaged uniformly over information messages with frozen vector $f$, and $P_e(N,K,A)$ for its further uniform average over $f$. Then
--
--   $$P_e(N,K,A)\le2\sqrt{\sum_{i\in A}\frac12\sqrt{F(W_N^{(i)})}},\qquad
--   \exists f:\quad P_e(N,K,A,f)\le2\sqrt{\sum_{i\in A}\frac12\sqrt{F(W_N^{(i)})}}.$$
--
--   The fidelity $F$ is squared fidelity. The result requires no polar selection rule and includes $A=\varnothing$, when every bit is frozen and block error is zero. It transfers split-channel reliability to an actual sequential decoder.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 6, Proposition 4: ensemble error bound and existence of a frozen vector

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4, PDF p.6; proof p.9. Both the frozen-vector average and
existence of a frozen vector are conclusions, for every information set.
The factor 2 is OUTSIDE sqrt and the factor 1/2 is INSIDE the sum. -/
theorem ensemble_error_bound {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (n : ℕ) (A : Finset (PolarWire n)) :
    ensembleError W n A ≤
      2 * Real.sqrt (∑ i ∈ A, (1 / 2 : ℝ) * Real.sqrt (squaredCqFidelity (splitChannel W n i))) ∧
    ∃ f : Frozen n A, frozenError W n A f ≤
      2 * Real.sqrt (∑ i ∈ A, (1 / 2 : ℝ) * Real.sqrt (squaredCqFidelity (splitChannel W n i))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
