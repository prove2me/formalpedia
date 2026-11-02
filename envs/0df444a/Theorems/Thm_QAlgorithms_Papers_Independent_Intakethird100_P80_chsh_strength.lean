-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_chsh_strength
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.chsh_strength
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:24:50.202751+00:00
-- url     : https://prove2.me/theorems/65dbcb64-e5f9-4068-ad1b-3c18d3b04578
-- title:
--   Exact CHSH saddle point and all three strengths
-- statement:
--   For the fixed CHSH experiment, outcomes are $T,F$ and the three settings $11,12,21$ favor equal outcomes, while $22$ favors unequal outcomes. Each favored outcome has probability $h=(2+\sqrt2)/8$ and each other outcome has probability $\ell=(2-\sqrt2)/8$. Let $\widetilde\pi$ put probability $1/8$ on each assignment $FFFF,TTTT,FFFT,TTTF,FFTF,TTFT,TFFT,FTTF$ in coordinate order $(x_1,x_2,y_1,y_2)$, and zero on all others. Let $\widetilde\sigma$ be uniform on the four settings.
--
--   The pair $(\widetilde\sigma,\widetilde\pi)$ is a saddle point in both the correlated and product games. The local strategy is an equalizer, and
--
--   $$S^{\rm UNI}_{\rm CHSH}=S^{\rm UC}_{\rm CHSH}=S^{\rm COR}_{\rm CHSH}=D_2(Q_{\widetilde\sigma}\|P_{\widetilde\sigma;\widetilde\pi})=2h\log_2\frac{h}{3/8}+2\ell\log_2\frac{\ell}{1/8}.$$
--
--   This evaluates the strength of this specified experiment, without optimizing quantum states or measurement directions.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 6, Example 4 and Appendix III-C: exact CHSH saddle point and all three strengths

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF pp.6,9,14–15,18,21: the specified CHSH saddle and all three EXACT strengths.
The decimal 0.0462738469 is not asserted as an exact value. -/
theorem chsh_strength :
    chshLocal ∈ stdSimplex ℝ (Potential BellScenario) ∧
    Saddle chshTable (stdSimplex ℝ (Settings BellScenario)) (uniformSettings BellScenario) chshLocal ∧
    Saddle chshTable (productSettings BellScenario) (uniformSettings BellScenario) chshLocal ∧
    (∀ s : Sigma BellScenario, statisticalPayoff chshTable s.1 chshLocal =
      statisticalPayoff chshTable (uniformSettings BellScenario) chshLocal) ∧
    uniformStrength chshTable = uncorrelatedStrength chshTable ∧
    uncorrelatedStrength chshTable = correlatedStrength chshTable ∧
    correlatedStrength chshTable = statisticalPayoff chshTable (uniformSettings BellScenario) chshLocal ∧
    correlatedStrength chshTable = ENNReal.ofReal (
      2 * (1 / 4 + Real.sqrt 2 / 8) * Real.logb 2 ((1 / 4 + Real.sqrt 2 / 8) / (3 / 8)) +
      2 * (1 / 4 - Real.sqrt 2 / 8) * Real.logb 2 ((1 / 4 - Real.sqrt 2 / 8) / (1 / 8))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
