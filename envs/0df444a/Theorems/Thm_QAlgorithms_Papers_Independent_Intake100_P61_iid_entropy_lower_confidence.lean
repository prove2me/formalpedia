-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_iid_entropy_lower_confidence
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.iid_entropy_lower_confidence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:05:43.946003+00:00
-- url     : https://prove2.me/theorems/8f5df4ac-87a1-4b42-ad7e-442df0ef2d99
-- title:
--   D29: lower confidence bound on finite-alphabet entropy
-- statement:
--   Let $p$ be a probability law on a finite alphabet of size $2^d$, where $d\ge0$ is an integer, and let $U_1,\ldots,U_n$ be iid samples with $n\ge2$. Write $\widehat p_a=n^{-1}\#\{i:U_i=a\}$, $\widehat H=-\sum_a\widehat p_a\log_2\widehat p_a$, and $H(p)=-\sum_a p_a\log_2p_a$, with $0\log_20=0$. For $0<\epsilon<1$,
--
--   $$\Pr\!\left[H(p)\le\widehat H-\sqrt{\frac{2(\log_2n)^2\ln(2/\epsilon)}{n}}\right]\le\epsilon.$$
--
--   Both entropies are one-symbol entropies in bits. This is the paper's lower confidence inference from D27–D28. **Source correction:** $n=1$ is excluded, since its zero radius makes the printed inclusive event certain for a deterministic law. D29 is physically on PDF page 18, despite the plan's page-17 anchor. Independent moderation remains pending.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 18, D26–D29

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.18, D29 following D26–D28 on pp.17–18: lower confidence bound
for one-symbol entropy. n>=2 corrects the false n=1 zero-radius inclusive event.
The singleton alphabet (d=0) is retained. Independent moderation is required. -/
theorem iid_entropy_lower_confidence
    (d n : ℕ) (hn : 2 ≤ n) (p : Fin (2 ^ d) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon < 1) :
    iidWordProbability p n (fun word =>
      (-∑ a, p a * Real.logb 2 (p a)) ≤ empiricalEntropy word -
        Real.sqrt (2 * (Real.logb 2 n) ^ 2 * Real.log (2 / epsilon) / n)) ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
