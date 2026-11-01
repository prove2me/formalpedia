-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_fastPolarization_poor
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.fastPolarization_poor
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:36:53.469926+00:00
-- url     : https://prove2.me/theorems/0c3a96de-4f31-4d58-9b55-18973f358e34
-- title:
--   Fast polarization toward poor commuting-output channels
-- statement:
--   Let $W:x\mapsto\rho_x$ be a binary cq channel on a finite nonempty register, and suppose $\rho_0\rho_1=\rho_1\rho_0$. For $N=2^n$, synthesize channels with the prescribed polar transform and let $f_i=\sqrt{F(W_N^{(i)})}$. For every real $\beta<1/2$,
--
--   $$
--   \lim_{n\to\infty}\frac{1}{2^n}\left|\left\{i:f_i>1-2^{-(2^n)^\beta}\right\}\right|=1-I(W).
--   $$
--
--   The strict inequality uses root fidelity. Uniform counting is the marginal probability of the fair synthesis process. This result supplies poor-channel polarization under commuting outputs and requires no degradation assumption.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 4, Proposition 4: fast polarization toward poor commuting channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.4–5, Proposition 4: strict poor threshold for ROOT fidelity; degradation
is not a hypothesis. Counting leaves is the independent fair birth-process marginal. -/
theorem fastPolarization_poor {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    (W : BinaryCQ H) (hW : IsBinaryCQ W) (hc : Commute (W false) (W true))
    (beta : ℝ) (hbeta : beta < 1 / 2) :
    Tendsto (fun n => leafProbability (poorSet W n beta)) atTop
      (nhds (1 - symmetricInformation W)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
