-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_fastPolarization_good
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.fastPolarization_good
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:34:32.793556+00:00
-- url     : https://prove2.me/theorems/eb7d631d-574f-4670-88a6-c06a4247c766
-- title:
--   Fast polarization toward good cq channels
-- statement:
--   Let $W:x\mapsto\rho_x$ be a binary-input cq channel with density operators on a finite nonempty quantum register. Write $I(W)=H((\rho_0+\rho_1)/2)-(H(\rho_0)+H(\rho_1))/2$, where $H$ is von Neumann entropy in bits. For $N=2^n$, form all $N$ synthesized channels using the row transform $G_N=B_NF_2^{\otimes n}$, and let $f_i=\sqrt{F(W_N^{(i)})}$ be their root fidelities. For every real $\beta<1/2$,
--
--   $$
--   \lim_{n\to\infty}\frac{1}{2^n}\left|\left\{i:f_i<2^{-(2^n)^\beta}\right\}\right|=I(W).
--   $$
--
--   Uniform choice among the synthesized leaves has exactly the marginal law of the independent fair-branch channel birth process. Thus this is the source's probability-limit assertion, including $\beta\le0$.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 3, Theorem 2: fast polarization toward good cq channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.3, Theorem 2: fair-branch marginal probability, expressed as uniform
counting over all 2^n synthesized leaves. The full printed beta range is retained. -/
theorem fastPolarization_good {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    (W : BinaryCQ H) (hW : IsBinaryCQ W) (beta : ℝ) (hbeta : beta < 1 / 2) :
    Tendsto (fun n => leafProbability (goodSet W n beta)) atTop
      (nhds (symmetricInformation W)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
