-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_conditional_exponent_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.conditional_exponent_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:52:56.558495+00:00
-- url     : https://prove2.me/theorems/e982746d-e3d9-4cbe-a639-ee9b0b4de04d
-- title:
--   Lemma 8 (73)
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. Let $0\le R<H(A|E)$, and define $e_\phi=\max_{0\le t\le1/2}[-\phi(t)-tR]$, $e_H=\max_{0\le s\le1}(g_E(s)-sR)/(1+s)$, and $\widetilde e_H=\max_{0\le s\le1}(g_E(s)-sR)/2$. Then
--   $$e_\phi\ge e_H\ge\widetilde e_H.$$
--   The first equality holds iff there is a maximizer $s_0\in[0,1]$ of $-\phi(s/(1+s))-sR/(1+s)$ for which $H_{1+s_0}(p_e)$ is almost surely constant. The second holds iff $e_H=(g_E(1)-R)/2$. This records the exceptions to strict improvement; the second condition uses the proof's correction $s=1$. The conditional Shannon entropy is $H(A|E)=-\int\sum_a p_e(a)\log p_e(a)\,d\mu(e)$, and $H_{1+s}(p_e)=-(1/s)\log\sum_a p_e(a)^{1+s}$ for $s>0$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 11, Lemma 8 (73)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.11–12, Lemma 8, (73). The unbound s in the second printed
condition is repaired to s=1, as explicitly stated by its proof on p.12. -/
theorem conditional_exponent_comparison {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (p : E → A → ℝ) (hp : IsConditionalLaw p) (R : ℝ)
    (hR : 0 ≤ R) (hent : R < integratedFiberEntropyNats mu p) :
    conditionalHExponent mu p R ≤ conditionalPhiExponent mu p R ∧
    conditionalTildeExponent mu p R ≤ conditionalHExponent mu p R ∧
    (conditionalPhiExponent mu p R = conditionalHExponent mu p R ↔
      ∃ s ∈ Set.Icc (0 : ℝ) 1,
        -conditionalPhi mu p (s / (1 + s)) - s * R / (1 + s) =
          conditionalPhiExponent mu p R ∧
        ∃ c : ℝ, ∀ᵐ e ∂mu, fiberRenyi (p e) s = c) ∧
    (conditionalHExponent mu p R = conditionalTildeExponent mu p R ↔
      conditionalHExponent mu p R = (conditionalRenyiNumerator mu p 1 - R) / 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
