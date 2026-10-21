-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_heterodyne_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P32.heterodyne_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:32:44.583372+00:00
-- url     : https://prove2.me/theorems/44534edd-d4a8-4b09-9891-7f18f90214fa
-- title:
--   Capacity under fixed heterodyne detection
-- statement:
--   Let $1/2<\eta\le1$ and $\bar N\ge0$. Alice uses product coherent-state modulation with codebook-average block energy at most $n\bar N$. The two receivers use the fixed single-use optical detection in the title, followed by measurable classical block decoders for their separate private messages. Messages are independent and uniform; the error is the average joint decoding error, as in Section II. Receiver noises are independent across uses and receivers. The observation in each use at a receiver with intensity $s$ is $\sqrt{s}A+Z$, where $Z$ is circular complex Gaussian noise with variance $1/2$ per real quadrature, hence $\mathbb E|Z|^2=1$.
--
--   The closure of the nonnegative rates achievable with vanishing error is the union over $0\le\beta\le1$ of the inequalities
--
--   $$
--   R_B\le\ln(1+\eta\beta\bar N),\qquad
--   R_C\le\ln\!\left(1+\frac{(1-\eta)(1-\beta)\bar N}{1+(1-\eta)\beta\bar N}\right).
--   $$
--
--   All rates are in nats per use. This is an unconditional receiver-restricted application of the classical Gaussian broadcast result, allowing arbitrary complex modulation under the photon budget and excluding collective optical measurement.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 6, Section V, Eqs. (38)-(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF p.6, (38)-(39): exact receiver-restricted capacity,
unconditionally, with single-use heterodyne measurements at both receivers.
The printed noise variance 1/2 is per real quadrature, consistent with these SNRs. -/
theorem heterodyne_capacity (eta Nbar : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    detectionRegion heterodyneLaw eta Nbar = heterodyneRateRegion eta Nbar := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
