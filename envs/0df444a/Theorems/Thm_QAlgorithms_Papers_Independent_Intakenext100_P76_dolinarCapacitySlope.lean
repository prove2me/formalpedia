-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_dolinarCapacitySlope
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.dolinarCapacitySlope
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:54:14.622422+00:00
-- url     : https://prove2.me/theorems/75246573-1ec5-4d29-8672-56b67b826f8c
-- title:
--   Corrected positive low-photon slope of the scalar Dolinar/BPSK capacity
-- statement:
--   For $x>0$, let $e(x)=(1-\sqrt{1-e^{-4x}})/2$ be the binary symmetric crossover probability in (6.17), and define $C_1(x)=(\ln2)[1-h_2(e(x))]$ in nats per mode. Then
--
--   $$
--   C_1(x)=2x+o(x),\qquad \lim_{x\downarrow0}\frac{C_1(x)}x=2.
--   $$
--
--   The sign printed in (6.18) is corrected from minus to plus: the exact capacity expression and the following two-nats-per-photon sentence fix the intended positive slope. This is a scalar asymptotic identity, without an additional receiver-optimality theorem.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 13, §6.2, corrected (6.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.13, corrected (6.18). Printed: -2 NS + o(NS). Changed: +2 NS + o(NS).
Reason: the exact nonnegative capacity preceding (6.18), and the following
"two nats per photon" sentence, both fix the positive sign. This scalar result
makes no assertion about physical optimality of a receiver. Independent
moderation of the source correction remains required. -/
theorem dolinarCapacitySlope :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun x : ℝ => dolinarNats x - 2 * x) (fun x : ℝ => x) ∧
    Tendsto (fun x : ℝ => dolinarNats x / x) (𝓝[>] 0) (𝓝 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
