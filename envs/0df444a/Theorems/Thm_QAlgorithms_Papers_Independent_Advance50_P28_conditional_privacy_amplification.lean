-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_conditional_privacy_amplification
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.conditional_privacy_amplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:51:19.309899+00:00
-- url     : https://prove2.me/theorems/2e1f1e21-ec34-4531-99d9-0a28791f6b0d
-- title:
--   Conditional privacy amplification (66)–(68)
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. Let an independent public seed choose a universal2 hash to $M\ge1$ symbols. For every $0\le t\le1/2$,
--   $$\mathbb E_Xd_1(P^{f_X(A),E},U_M\otimes P^E)=d_1(P^{K,E,X},U_M\otimes P^E\otimes P^X)\le3M^te^{\phi(t)}.$$
--   For each such $t$ there also exists a deterministic hash with the same bound. This makes public-seed security explicit; arbitrary conditional vectors on null fibers are ignored.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 10, Conditional privacy amplification (66)–(68)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.10, (66)–(68): measurable side information and a public independent seed. -/
theorem conditional_privacy_amplification {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (p : E → A → ℝ) (hp : IsConditionalLaw p)
    {M : ℕ} (hM : 0 < M) (h : HashEnsemble A M) (hu : Universal2 h) :
    expectedConditionalLeakage mu p h = publicSeedLeakage mu p h ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), expectedConditionalLeakage mu p h ≤
      3 * (M : ℝ) ^ t * Real.exp (conditionalPhi mu p t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ f : A → Fin M,
      conditionalLeakage mu p f ≤ 3 * (M : ℝ) ^ t * Real.exp (conditionalPhi mu p t)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
