-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P04_orderedIndividualSaturation
-- name    : QAlgorithms.Papers.Independent.Frontier18.P04.orderedIndividualSaturation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:53:12.892659+00:00
-- url     : https://prove2.me/theorems/d54afdd4-f9f4-47df-80c1-9cb57ab8cbf7
-- title:
--   Ordered high-energy individual-rate saturation
-- statement:
--   Fix $0<\eta\le1$. For $a>0$ choose Alice's squeeze $z(a)=\tfrac12\log(2a+1)$; it is nonnegative and satisfies $\sinh^2z(a)\le a$. For every helper budget $b\ge0$, use Bob's zero-message squeezed seed with $Z(b)=\operatorname{arsinh}\sqrt b$. Let $R_1(\eta,a,b,z)$ be the homodyne rate in (81), and let $g$ be the thermal entropy in nats. This selected code achieves $R_1(\eta,a,b,z(a))$ for each $a,b$ and satisfies
--
--   $$
--   \begin{aligned}
--   \lim_{b\to\infty}\frac{R_1(\eta,a,b,z(a))}{g(a)}&=\frac{\log(1+2a)}{g(a)}\quad(a>0),\\
--   \lim_{a\to\infty}\frac{\log(1+2a)}{g(a)}&=1.
--   \end{aligned}
--   $$
--
--   Thus Bob's budget tends to infinity first, at fixed Alice budget, before Alice's budget tends to infinity. The statement neither identifies a joint limit along arbitrary paths nor claims that both senders attain their individual bounds simultaneously. It records a relative-rate limit, with a feasible operational code at every finite pair of budgets.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, PDF p. 10, §V, (82)–(84): iterated high-photon individual-rate saturation

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- arXiv:quant-ph/0506171v2, PDF p.10,(82)–(84): ordered individual-rate
saturation by the selected feasible squeezed-helper code. Bob's photon budget tends
to infinity first, at each fixed positive Alice budget. Only then does Alice's budget
tend to infinity. This is neither a simultaneous two-user rate assertion nor a joint
limit along arbitrary paths, and the selected squeeze is not a finite-nB optimum. -/
theorem orderedIndividualSaturation (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    (∀ nA nB : ℝ, 0 < nA → 0 ≤ nB →
      0 ≤ selectedSqueeze nA ∧ (Real.sinh (selectedSqueeze nA)) ^ 2 ≤ nA ∧
      (fun _ : Fin 1 => helperRate eta nA nB (selectedSqueeze nA))
        ∈ helperCapacity eta nA nB (selectedSqueeze nA)) ∧
    (∀ nA : ℝ, 0 < nA →
      Tendsto (fun nB : ℝ => helperRate eta nA nB (selectedSqueeze nA) / thermalEntropy nA)
        atTop (𝓝 (Real.log (1 + 2 * nA) / thermalEntropy nA))) ∧
    Tendsto (fun nA : ℝ => Real.log (1 + 2 * nA) / thermalEntropy nA)
      atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P04

end
