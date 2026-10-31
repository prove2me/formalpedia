-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_decoherence_exponentCrossover
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.decoherence_exponentCrossover
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:30:31.620216+00:00
-- url     : https://prove2.me/theorems/5f390a18-b0b5-4336-853a-48972cf86672
-- title:
--   §7.4.3: relative size of quantum and dispersion decoherence factors
-- statement:
--   Let $M,\beta,\hbar,\eta,t>0$ and $\Delta P\ne0$. With $D_{pp}=\eta M/\beta$ and $D_{xx}=\eta\beta\hbar^2/(16M)$, let $q=D_{xx}|\Delta P|^2t/\hbar^2$ and $d=D_{pp}|\Delta P|^2t^3/(12M^2\hbar^2)$. Then
--   $$
--   \frac dq=\frac{4t^2}{3\beta^2\hbar^2},\qquad q\le d\ \Longleftrightarrow\ t\ge\frac{\sqrt3}{2}\beta\hbar.
--   $$
--   This is the exact comparison of the two factors discussed in the source. It neither asserts a corrected full momentum-kernel solution nor strengthens the source's approximate time scale into a general dynamical limit.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 44, §7.4.3: relative size of quantum and dispersion decoherence factors

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.43–44, Section 7.4.3: exact comparison of the two explicitly
displayed factors; it does not endorse the defective full-kernel formula. -/
theorem decoherence_exponentCrossover (M beta hbar eta t : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (hhbar : 0 < hbar) (heta : 0 < eta)
    (ht : 0 < t) (delta : Momentum) (hdelta : delta ≠ 0) :
    dispersionExponent M beta hbar eta t delta / quantumExponent M beta eta t delta =
      4 / 3 * (t / (beta * hbar)) ^ 2 ∧
    (quantumExponent M beta eta t delta ≤ dispersionExponent M beta hbar eta t delta ↔
      Real.sqrt 3 * beta * hbar / 2 ≤ t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
