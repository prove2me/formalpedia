-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_general_additive_channel_identities
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.general_additive_channel_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:57:33.45796+00:00
-- url     : https://prove2.me/theorems/26983d74-a793-4b5f-8fed-3f86037ef060
-- title:
--   General additive-channel identities (82)–(86)
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. Let $A=G$ be a finite abelian additive group and let $W_x(z,e)=p_e(z-x)$ be the channel density relative to counting measure times $\mu$. Under uniform input,
--   $$\phi(t|W,U_G)=t\log|G|+\phi(t),\qquad\psi(s|W,U_G)=s\log|G|-g_E(s).$$
--   The first identity is stated for $0\le t\le1/2$ and the second for all $s\ge0$. Consequently, at $u=\log|G|-R$, the channel exponents $e_\phi,e_\psi,\widetilde e_\psi$ equal respectively the conditional source exponents $e_\phi(u),e_H(u),\widetilde e_H(u)$ defined above. The noise law is genuinely conditional, including measurable side noise. The channel exponents mean $e_\phi(R)=\sup_{0\le t\le1/2}[tR-\phi(t)]$, $e_\psi(R)=\sup_{0\le s\le1}(sR-\psi(s))/(1+s)$ and $\widetilde e_\psi(R)=\sup_{0\le s\le1}(sR-\psi(s))/2$. For a source rate $u$, $e_\phi(u)=\max_{0\le t\le1/2}[-\phi(t)-tu]$, $e_H(u)=\max_{0\le s\le1}(g_E(s)-su)/(1+s)$, and $\widetilde e_H(u)=\max_{0\le s\le1}(g_E(s)-su)/2$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 15, General additive-channel identities (82)–(86)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.15, (82)–(86): conditional Renyi quantities for joint additive
noise, with no silent restriction to a finite side-noise alphabet. -/
theorem general_additive_channel_identities {G E : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (p : E → G → ℝ)
    (hp : IsConditionalLaw p) (R : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ENNReal.log
      (gallagerDensityMoment (Measure.count.prod mu) (generalAdditiveDensity p) (finiteUniformMass G) t) =
        ((t * Real.log (Fintype.card G : ℝ) + conditionalPhi mu p t : ℝ) : EReal)) ∧
    (∀ s : ℝ, 0 ≤ s → ENNReal.log
      (psiMoment (Measure.count.prod mu) (generalAdditiveDensity p) (finiteUniformMass G) s) =
        ((s * Real.log (Fintype.card G : ℝ) - conditionalRenyiNumerator mu p s : ℝ) : EReal)) ∧
    wiretapPhiExponent (Measure.count.prod mu) (generalAdditiveDensity p) (finiteUniformMass G) R =
      (conditionalPhiExponent mu p (Real.log (Fintype.card G : ℝ) - R) : EReal) ∧
    wiretapPsiExponent (Measure.count.prod mu) (generalAdditiveDensity p) (finiteUniformMass G) R =
      (conditionalHExponent mu p (Real.log (Fintype.card G : ℝ) - R) : EReal) ∧
    wiretapTildeExponent (Measure.count.prod mu) (generalAdditiveDensity p) (finiteUniformMass G) R =
      (conditionalTildeExponent mu p (Real.log (Fintype.card G : ℝ) - R) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
