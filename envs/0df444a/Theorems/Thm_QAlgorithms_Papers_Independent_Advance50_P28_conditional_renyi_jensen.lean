-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_conditional_renyi_jensen
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.conditional_renyi_jensen
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:52:25.704243+00:00
-- url     : https://prove2.me/theorems/3e11399d-2922-4924-b284-ac9a195df3d4
-- title:
--   Lemma 7 (72)
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. For every $s>0$,
--   $$\phi\!\left(\frac{s}{1+s}\right)\le-\frac{g_E(s)}{1+s}.$$
--   Equality holds exactly when $e\mapsto H_{1+s}(p_e)=-(1/s)\log\sum_ap_e(a)^{1+s}$ is constant almost surely. This is the paper's Jensen comparison, with the support condition interpreted measure-theoretically.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 11, Lemma 7 (72)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.11, Lemma 7, (72): equality is almost-sure constancy for a
measurable Eve alphabet; no optimized quantum conditional entropy is substituted. -/
theorem conditional_renyi_jensen {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (p : E → A → ℝ) (hp : IsConditionalLaw p) (s : ℝ) (hs : 0 < s) :
    conditionalPhi mu p (s / (1 + s)) ≤ -conditionalRenyiNumerator mu p s / (1 + s) ∧
    (conditionalPhi mu p (s / (1 + s)) = -conditionalRenyiNumerator mu p s / (1 + s) ↔
      ∃ c : ℝ, ∀ᵐ e ∂mu, fiberRenyi (p e) s = c) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
