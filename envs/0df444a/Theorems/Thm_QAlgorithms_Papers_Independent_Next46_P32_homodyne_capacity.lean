-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_homodyne_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P32.homodyne_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:32:10.154188+00:00
-- url     : https://prove2.me/theorems/ab3139ce-4574-4d90-b5f8-529aa77137cc
-- title:
--   Capacity under fixed homodyne detection
-- statement:
--   Let $1/2<\eta\le1$ and $\bar N\ge0$. Alice uses product coherent-state modulation with codebook-average block energy at most $n\bar N$. The two receivers use the fixed single-use optical detection in the title, followed by measurable classical block decoders for their separate private messages. Messages are independent and uniform; the error is the average joint decoding error, as in Section II. Receiver noises are independent across uses and receivers. The observation in each use at a receiver with intensity $s$ is $\sqrt{s}\operatorname{Re}A+V$, where $V$ is real Gaussian noise of variance $1/4$.
--
--   The closure of the nonnegative rates achievable with vanishing error is the union over $0\le\beta\le1$ of the inequalities
--
--   $$
--   R_B\le\tfrac12\ln(1+4\eta\beta\bar N),\qquad
--   R_C\le\tfrac12\ln\!\left(1+\frac{4(1-\eta)(1-\beta)\bar N}{1+4(1-\eta)\beta\bar N}\right).
--   $$
--
--   All rates are in nats per use. This is an unconditional receiver-restricted application of the classical Gaussian broadcast result, allowing arbitrary complex modulation under the photon budget and excluding collective optical measurement.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 6, Section V, Eqs. (36)-(37), PDF pp.5-6

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

/-- Section V, PDF pp.5-6, (36)-(37): exact receiver-restricted capacity,
unconditionally. Only real-quadrature homodyne optical detection is permitted;
classical processing may use the entire observation block. -/
theorem homodyne_capacity (eta Nbar : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    detectionRegion homodyneLaw eta Nbar = homodyneRateRegion eta Nbar := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
