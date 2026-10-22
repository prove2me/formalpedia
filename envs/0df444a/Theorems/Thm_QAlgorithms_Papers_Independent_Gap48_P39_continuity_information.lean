-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_continuity_information
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.continuity_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:18:11.15062+00:00
-- url     : https://prove2.me/theorems/6cd5d744-095e-4a45-914d-dd1702a33c1d
-- title:
--   Lemma 3: continuity of conditional entropy and mutual information
-- statement:
--   Let $\rho^{AB},\sigma^{AB}$ be positive trace-one density matrices on the same positive-dimensional finite bipartite system. Let $0\le\delta\le1/e$ and suppose their full trace-norm distance is at most $\delta$. Then
--
--   $$|H(A\mid B)_\rho-H(A\mid B)_\sigma|\le2H_2(\delta)+4\delta\log_2|AB|,$$
--
--   $$|I(A;B)_\rho-I(A;B)_\sigma|\le3H_2(\delta)+6\delta\log_2|AB|.$$
--
--   Here $H_2$ is binary entropy, $|AB|$ is the product dimension, $H(A\mid B)=H(AB)-H(B)$, and $I(A;B)=H(A)+H(B)-H(AB)$, with actual partial traces and base-two von Neumann entropy. Both bounds include $\delta=0$ and singleton systems. These continuity estimates use the full norm, without a factor of one half.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 10, Lemma 3: continuity of conditional entropy and mutual information

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Lemma 3, PDF p.10: absolute differences; full trace norm and base-two logs. -/
theorem continuity_information [Nonempty A] [Nonempty B]
    (rho sigma : Op (A × B)) (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma)
    (delta : ℝ) (h0 : 0 ≤ delta) (h1 : delta ≤ 1 / Real.exp 1)
    (hclose : traceNorm (rho - sigma) ≤ delta) :
    |conditionalEntropy rho - conditionalEntropy sigma| ≤
      2 * binEntropy2 delta + 4 * delta * Real.logb 2 (Fintype.card (A × B)) ∧
    |mutualInformation rho - mutualInformation sigma| ≤
      3 * binEntropy2 delta + 6 * delta * Real.logb 2 (Fintype.card (A × B)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
