-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_coherent_bright_noise_exponent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.coherent_bright_noise_exponent
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:19:55.954395+00:00
-- url     : https://prove2.me/theorems/b04738a1-2403-4f5e-ae4e-2ef25d9386ed
-- title:
--   Eq.(12): bright-noise leading coherent exponent
-- statement:
--   Fix $0<\kappa<1$ and $N_S\ge0$. Let $c(\kappa,N_S,N_B)=\kappa N_S(\sqrt{N_B+1}-\sqrt{N_B})^2$ be the exact exponent coefficient in the coherent Chernoff upper bound. Then
--   $$
--   \lim_{N_B\to\infty}N_B\,c(\kappa,N_S,N_B)=\frac{\kappa N_S}{4}.
--   $$
--   This pins the leading bright-noise coefficient in Eq.(12). It does not specify a simultaneous copy-number limit or a uniform relative approximation of exponentially small error bounds.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 3, Eq.(12): bright-noise leading coherent exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.3, Eq.(12): leading coefficient of the coherent upper-bound
exponent as NB tends to infinity, with k and NS fixed. No uniform relative
approximation of exponentials for arbitrarily growing M is asserted. -/
theorem coherent_bright_noise_exponent (k NS : ℝ)
    (hk : 0 < k) (hk1 : k < 1) (hNS : 0 ≤ NS) :
    Tendsto (fun NB : ℝ => NB * coherentExponent k NS NB)
      atTop (nhds (k * NS / 4)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
