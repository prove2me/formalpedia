-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P04_heterodyneSumRatio
-- name    : QAlgorithms.Papers.Independent.Frontier18.P04.heterodyneSumRatio
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:51:54.103691+00:00
-- url     : https://prove2.me/theorems/baddbba7-4e6c-4b19-8d92-4b1635860c4b
-- title:
--   Heterodyne sum rate approaches the ultimate sum bound in ratio
-- statement:
--   For $0\le\eta\le1$ and photon budgets $\bar n_A,\bar n_B\ge0$, let $\mathcal C_{\rm het}$ be the operational heterodyne coherent-state region and put $x=\eta\bar n_A+(1-\eta)\bar n_B$. Its set of rate sums has an attained greatest element $\log(1+x)$. With natural logarithms and $g(x)=(x+1)\log(x+1)-x\log x$, where $0\log0=0$,
--
--   $$
--   \max_{(R_1,R_2)\in\mathcal C_{\rm het}}(R_1+R_2)=\log(1+x),\qquad
--   \lim_{x\to\infty}\frac{\log(1+x)}{g(x)}=1.
--   $$
--
--   Here $g(x)$ is the source's ultimate sum-rate bound (80). Thus heterodyne reception attains that scale asymptotically in relative rate; this does not assert a vanishing additive gap. The greatest-element assertion uses actual codes through the measured capacity object, rather than defining that object by the logarithmic formula.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, PDF p. 9, §V: high-power heterodyne sum-rate optimality

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- arXiv:quant-ph/0506171v2, PDF p.9, paragraph after (80): heterodyne has
asymptotically optimal sum rate in the ratio sense. The maximum in the measured
region is attained, and its ratio to the source's ultimate sum bound g(x) tends
to one as received power x tends to infinity. No vanishing additive gap is claimed. -/
theorem heterodyneSumRatio :
    (∀ eta nA nB : ℝ, 0 ≤ eta → eta ≤ 1 → 0 ≤ nA → 0 ≤ nB →
      IsGreatest (heterodyneSums eta nA nB) (Real.log (1 + eta * nA + (1 - eta) * nB))) ∧
    Tendsto (fun x : ℝ => Real.log (1 + x) / thermalEntropy x) atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P04

end
