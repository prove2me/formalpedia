-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_ghz_strength
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.ghz_strength
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:25:38.435323+00:00
-- url     : https://prove2.me/theorems/556f2e45-af8d-41f9-8477-a7bd40286794
-- title:
--   Exact GHZ strengths and optimal sampling laws
-- statement:
--   Use the fixed GHZ experiment of Appendix III-F. On settings $111,122,212,221$, four allowed parity outcomes have probability $1/4$ each: the number of $T$ outcomes is odd at $111$ and even at the other three settings. At all other settings every outcome has probability $1/8$. Let $\sigma^\circ$ sample all eight settings uniformly and let $\sigma^*$ assign probability $1/4$ to each of the four parity settings.
--
--   The uniform law is optimal among product setting laws, while $\sigma^*$ is optimal among all setting laws, and
--
--   $$S^{\rm UNI}_{\rm GHZ}=S^{\rm UC}_{\rm GHZ}=\tfrac12\log_2(4/3),\qquad S^{\rm COR}_{\rm GHZ}=\log_2(4/3).$$
--
--   A single local law realizes Table XXIX at every setting: its probabilities at a parity setting are $3/16$ on allowed outcomes and $1/16$ on the others, and are $1/8$ at other settings. This law is optimal for both displayed setting laws.
--
--   The four settings and the $1/4$ masses follow Table XXVIII and equation (35); the p.24 prose mistakenly prints $(0.125,0)$ and an even number of setting-1 measurements. This statement corrects those two typos and makes no factor-4.5 comparison.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 8, Appendix III-F: optimal GHZ setting laws and exact strengths

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF pp.8,17,21,24: exact GHZ optima, optimal setting laws and a common realizing
local law for Table XXIX. The p.24 prose typos are corrected as documented above.
No equality or literal lower bound with the factor 4.5 is claimed. -/
theorem ghz_strength :
    ghzCorrelatedSettings ∈ stdSimplex ℝ (Settings GHZScenario) ∧
    Uncorrelated (uniformSettings GHZScenario) ∧
    uniformStrength ghzTable = uncorrelatedStrength ghzTable ∧
    uncorrelatedStrength ghzTable = ENNReal.ofReal (Real.logb 2 (4 / 3) / 2) ∧
    lowerValue ghzTable ghzCorrelatedSettings = correlatedStrength ghzTable ∧
    correlatedStrength ghzTable = ENNReal.ofReal (Real.logb 2 (4 / 3)) ∧
    ∃ p : PiLocal GHZScenario, localTable p.1 = ghzLocalTable ∧
      statisticalPayoff ghzTable (uniformSettings GHZScenario) p.1 = uniformStrength ghzTable ∧
      statisticalPayoff ghzTable ghzCorrelatedSettings p.1 = correlatedStrength ghzTable := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
